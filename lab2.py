import os
import tkinter as tk
from tkinter import ttk, filedialog, messagebox
from tkinter.scrolledtext import ScrolledText


def advance_lfsr_state(state: int, steps: int) -> int:
    for _ in range(steps):
        feedback_bit = ((state >> 31) ^ (state >> 27) ^ (state >> 26) ^ state) & 1
        state = (state >> 1) | (feedback_bit << 31)
    return state


def build_lfsr_transition_tables(steps: int):
    return tuple(
        tuple(advance_lfsr_state(value << shift, steps) for value in range(256))
        for shift in (0, 8, 16, 24)
    )


REVERSED_BYTE = bytes(int(f'{value:08b}'[::-1], 2) for value in range(256))
TRANSITION_TABLES_8 = build_lfsr_transition_tables(8)
TRANSITION_TABLES_32 = build_lfsr_transition_tables(32)
REVERSED_WORD16 = tuple(
    REVERSED_BYTE[value & 0xff] | (REVERSED_BYTE[(value >> 8) & 0xff] << 8)
    for value in range(65536)
)
TRANSITION32_LOW16 = tuple(
    TRANSITION_TABLES_32[0][value & 0xff] ^ TRANSITION_TABLES_32[1][value >> 8]
    for value in range(65536)
)
TRANSITION32_HIGH16 = tuple(
    TRANSITION_TABLES_32[2][value & 0xff] ^ TRANSITION_TABLES_32[3][value >> 8]
    for value in range(65536)
)


def transition32_from_tables(state: int) -> int:
    return TRANSITION32_LOW16[state & 0xffff] ^ TRANSITION32_HIGH16[state >> 16]


def key_word32_from_state(state: int) -> int:
    return REVERSED_WORD16[state & 0xffff] | (REVERSED_WORD16[state >> 16] << 16)


KEY64_LOW16 = tuple(
    key_word32_from_state(value) | (key_word32_from_state(transition32_from_tables(value)) << 32)
    for value in range(65536)
)
KEY64_HIGH16 = tuple(
    key_word32_from_state(value << 16) | (key_word32_from_state(transition32_from_tables(value << 16)) << 32)
    for value in range(65536)
)
TRANSITION64_LOW16 = tuple(
    transition32_from_tables(transition32_from_tables(value))
    for value in range(65536)
)
TRANSITION64_HIGH16 = tuple(
    transition32_from_tables(transition32_from_tables(value << 16))
    for value in range(65536)
)


class LFSR32:
    """
    LFSR for polynomial x^32 + x^28 + x^27 + x + 1.

    State is stored as a 32-bit integer matching bits [b31, b30, ..., b0].
    Output bit = rightmost bit b0.
    New bit = b31 XOR b27 XOR b26 XOR b0.
    Shift right each tick.
    """

    SIZE = 32
    REVERSED_BYTE = REVERSED_BYTE
    TRANSITION_TABLES_8 = TRANSITION_TABLES_8
    REVERSED_WORD16 = REVERSED_WORD16
    TRANSITION32_LOW16 = TRANSITION32_LOW16
    TRANSITION32_HIGH16 = TRANSITION32_HIGH16
    KEY64_LOW16 = KEY64_LOW16
    KEY64_HIGH16 = KEY64_HIGH16
    TRANSITION64_LOW16 = TRANSITION64_LOW16
    TRANSITION64_HIGH16 = TRANSITION64_HIGH16

    def __init__(self, state_bits: str):
        if len(state_bits) != self.SIZE or any(ch not in '01' for ch in state_bits):
            raise ValueError("Начальное состояние должно содержать ровно 32 символа 0/1.")
        if set(state_bits) == {'0'}:
            raise ValueError("Начальное состояние не может состоять только из нулей.")
        self.state = int(state_bits, 2)

    def get_state_str(self) -> str:
        return f'{self.state:032b}'

    def step(self):
        old_state = self.state
        output_bit = old_state & 1
        feedback_bit = ((old_state >> 31) ^ (old_state >> 27) ^ (old_state >> 26) ^ old_state) & 1
        self.state = (old_state >> 1) | (feedback_bit << 31)
        old_bits = [int(ch) for ch in f'{old_state:032b}']
        new_bits = [int(ch) for ch in f'{self.state:032b}']
        return output_bit, feedback_bit, old_bits, new_bits

    def generate_bits(self, count: int) -> str:
        bits = []
        state = self.state
        for _ in range(count):
            output_bit = state & 1
            feedback_bit = ((state >> 31) ^ (state >> 27) ^ (state >> 26) ^ state) & 1
            state = (state >> 1) | (feedback_bit << 31)
            bits.append(str(output_bit))
        self.state = state
        return ''.join(bits)

    def generate_byte(self) -> int:
        state = self.state
        value = self.REVERSED_BYTE[state & 0xff]
        table0, table1, table2, table3 = self.TRANSITION_TABLES_8
        self.state = (
            table0[state & 0xff]
            ^ table1[(state >> 8) & 0xff]
            ^ table2[(state >> 16) & 0xff]
            ^ table3[(state >> 24) & 0xff]
        )
        return value

    def xor_chunk(self, chunk: bytes, preview_count: int = 0) -> tuple[bytes, bytes]:
        state = self.state
        chunk_length = len(chunk)
        result = bytearray(chunk_length)
        key_preview = bytearray()
        append_key = key_preview.append
        reversed_byte = self.REVERSED_BYTE
        table8_0, table8_1, table8_2, table8_3 = self.TRANSITION_TABLES_8
        key64_low16 = self.KEY64_LOW16
        key64_high16 = self.KEY64_HIGH16
        transition64_low16 = self.TRANSITION64_LOW16
        transition64_high16 = self.TRANSITION64_HIGH16

        for index in range(preview_count):
            byte = chunk[index]
            key_byte = reversed_byte[state & 0xff]
            state = (
                table8_0[state & 0xff]
                ^ table8_1[(state >> 8) & 0xff]
                ^ table8_2[(state >> 16) & 0xff]
                ^ table8_3[(state >> 24) & 0xff]
            )

            result[index] = byte ^ key_byte
            append_key(key_byte)

        group_end = chunk_length - ((chunk_length - preview_count) % 8)
        if group_end > preview_count:
            source_words = memoryview(chunk)[preview_count:group_end].cast('Q')
            result_words = memoryview(result)[preview_count:group_end].cast('Q')
            for word_index, source_word in enumerate(source_words):
                low16 = state & 0xffff
                high16 = state >> 16
                result_words[word_index] = source_word ^ (key64_low16[low16] ^ key64_high16[high16])
                state = transition64_low16[low16] ^ transition64_high16[high16]

            source_words.release()
            result_words.release()

        for index in range(group_end, chunk_length):
            byte = chunk[index]
            key_byte = reversed_byte[state & 0xff]
            state = (
                table8_0[state & 0xff]
                ^ table8_1[(state >> 8) & 0xff]
                ^ table8_2[(state >> 16) & 0xff]
                ^ table8_3[(state >> 24) & 0xff]
            )

            result[index] = byte ^ key_byte

        self.state = state
        return bytes(result), bytes(key_preview)


def bytes_to_bit_string(data: bytes) -> str:
    return ''.join(f'{byte:08b}' for byte in data)


def xor_bytes(data: bytes, key_bits: str) -> bytes:
    result = bytearray()
    for i, byte in enumerate(data):
        key_byte_bits = key_bits[i * 8:(i + 1) * 8]
        key_byte = int(key_byte_bits, 2)
        result.append(byte ^ key_byte)
    return bytes(result)


class App(tk.Tk):
    DISPLAY_BYTE_LIMIT = 60
    FILE_CHUNK_SIZE = 8 * 1024 * 1024

    def __init__(self):
        super().__init__()
        self.title("Потоковое шифрование LFSR — вариант 10")
        self.geometry("1300x850")
        self.minsize(1100, 760)

        self.input_path = tk.StringVar()
        self.output_path = tk.StringVar()
        self.state_var = tk.StringVar()
        self.status_var = tk.StringVar(value="Выберите файл, введите состояние регистра из 32 бит и нажмите нужную кнопку.")

        self._build_ui()
        self.state_var.trace_add('write', self._filter_state_bits)

    def _build_ui(self):
        top = ttk.Frame(self, padding=10)
        top.pack(fill=tk.X)

        title = ttk.Label(
            top,
            text="Система потокового шифрования / дешифрования файла на основе LFSR",
            font=("Segoe UI", 15, "bold")
        )
        title.pack(anchor='w')

        subtitle = ttk.Label(
            top,
            text="Полином: x^32 + x^28 + x^27 + x + 1   |   Размер регистра: 32 бита",
            font=("Segoe UI", 10)
        )
        subtitle.pack(anchor='w', pady=(4, 0))

        params = ttk.LabelFrame(self, text="Параметры", padding=10)
        params.pack(fill=tk.X, padx=10, pady=5)

        ttk.Label(params, text="Начальное состояние регистра (32 бита):").grid(row=0, column=0, sticky='w', padx=5, pady=5)
        self.state_entry = ttk.Entry(params, textvariable=self.state_var, width=50)
        self.state_entry.grid(row=0, column=1, sticky='we', padx=5, pady=5)
        ttk.Label(params, text="Вводятся только символы 0 и 1").grid(row=0, column=2, sticky='w', padx=5, pady=5)

        ttk.Label(params, text="Исходный файл:").grid(row=1, column=0, sticky='w', padx=5, pady=5)
        ttk.Entry(params, textvariable=self.input_path).grid(row=1, column=1, sticky='we', padx=5, pady=5)
        ttk.Button(params, text="Обзор...", command=self.choose_input_file).grid(row=1, column=2, sticky='ew', padx=5, pady=5)

        ttk.Label(params, text="Файл результата:").grid(row=2, column=0, sticky='w', padx=5, pady=5)
        ttk.Entry(params, textvariable=self.output_path).grid(row=2, column=1, sticky='we', padx=5, pady=5)
        ttk.Button(params, text="Сохранить как...", command=self.choose_output_file).grid(row=2, column=2, sticky='ew', padx=5, pady=5)

        params.columnconfigure(1, weight=1)

        buttons = ttk.Frame(self, padding=(10, 0, 10, 5))
        buttons.pack(fill=tk.X)

        ttk.Button(buttons, text="Зашифровать файл", command=self.encrypt_file).pack(side=tk.LEFT, padx=5, pady=5)
        ttk.Button(buttons, text="Расшифровать файл", command=self.decrypt_file).pack(side=tk.LEFT, padx=5, pady=5)
        ttk.Button(buttons, text="Очистить поля вывода", command=self.clear_output).pack(side=tk.LEFT, padx=5, pady=5)

        ttk.Label(buttons, textvariable=self.status_var, foreground="blue").pack(side=tk.LEFT, padx=15)

        out_notebook = ttk.Notebook(self)
        out_notebook.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)

        key_tab = ttk.Frame(out_notebook)
        source_tab = ttk.Frame(out_notebook)
        encrypted_tab = ttk.Frame(out_notebook)

        out_notebook.add(key_tab, text="Ключ")
        out_notebook.add(source_tab, text="Исходный файл (биты)")
        out_notebook.add(encrypted_tab, text="Результат (биты)")

        self.key_text = ScrolledText(key_tab, wrap=tk.WORD, font=("Consolas", 10), exportselection=False)
        self.key_text.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        self._configure_output_text(self.key_text)

        self.source_bits_text = ScrolledText(source_tab, wrap=tk.WORD, font=("Consolas", 10), exportselection=False)
        self.source_bits_text.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        self._configure_output_text(self.source_bits_text)

        self.result_bits_text = ScrolledText(encrypted_tab, wrap=tk.WORD, font=("Consolas", 10), exportselection=False)
        self.result_bits_text.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        self._configure_output_text(self.result_bits_text)

    def _configure_output_text(self, widget):
        widget.bind("<Control-a>", self._select_all_text)
        widget.bind("<Control-A>", self._select_all_text)
        widget.bind("<Control-c>", self._copy_selection)
        widget.bind("<Control-C>", self._copy_selection)
        widget.bind("<Control-KeyPress>", self._handle_text_shortcut)
        widget.bind("<<Copy>>", self._copy_selection)
        widget.bind("<Button-3>", self._show_text_menu)

    def _handle_text_shortcut(self, event):
        key = event.keysym.lower()
        if event.keycode == 65 or key in ("a", "ф"):
            return self._select_all_text(event)
        if event.keycode == 67 or key in ("c", "с", "cyrillic_es"):
            return self._copy_selection(event)
        return None

    def _select_all_text(self, event):
        event.widget.tag_add(tk.SEL, "1.0", tk.END)
        event.widget.mark_set(tk.INSERT, "1.0")
        event.widget.see(tk.INSERT)
        return "break"

    def _copy_selection(self, event):
        widget = event.widget
        try:
            text = widget.get(tk.SEL_FIRST, tk.SEL_LAST)
        except tk.TclError:
            ranges = widget.tag_ranges(tk.SEL)
            if len(ranges) < 2:
                return "break"
            text = widget.get(ranges[0], ranges[1])
        if not text:
            return "break"
        self._copy_to_clipboard(text)
        return "break"

    def _show_text_menu(self, event):
        event.widget.focus_set()
        menu = tk.Menu(self, tearoff=0)
        menu.add_command(label="Копировать", command=lambda: self.copy_selected_text(event.widget))
        try:
            menu.tk_popup(event.x_root, event.y_root)
        finally:
            menu.grab_release()
        return "break"

    def copy_selected_text(self, widget):
        try:
            text = widget.get(tk.SEL_FIRST, tk.SEL_LAST)
        except tk.TclError:
            text = ""
        if text:
            self._copy_to_clipboard(text)

    def _copy_to_clipboard(self, text: str):
        self.clipboard_clear()
        self.clipboard_append(text)
        self.update()
        self.status_var.set("Данные скопированы в буфер обмена.")

    def _filter_state_bits(self, *args):
        value = self.state_var.get()
        filtered = ''.join(ch for ch in value if ch in '01')[:32]
        if value != filtered:
            self.state_var.set(filtered)

    def choose_input_file(self):
        path = filedialog.askopenfilename(title="Выберите исходный файл")
        if path:
            self.input_path.set(path)
            if not self.output_path.get():
                directory, filename = os.path.split(path)
                self.output_path.set(os.path.join(directory, f"result_{filename}"))

    def choose_output_file(self):
        path = filedialog.asksaveasfilename(title="Укажите файл результата")
        if path:
            self.output_path.set(path)

    def _validate_inputs(self):
        state = self.state_var.get()
        if len(state) != 32:
            messagebox.showerror("Ошибка", "Начальное состояние должно содержать ровно 32 бита.")
            return None
        if set(state) == {'0'}:
            messagebox.showerror("Ошибка", "Начальное состояние не может быть полностью нулевым.")
            return None

        input_path = self.input_path.get().strip()
        if not input_path or not os.path.isfile(input_path):
            messagebox.showerror("Ошибка", "Выберите существующий исходный файл.")
            return None

        output_path = self.output_path.get().strip()
        if not output_path:
            messagebox.showerror("Ошибка", "Укажите путь для сохранения результата.")
            return None

        return state, input_path, output_path

    def clear_output(self):
        for widget in (self.key_text, self.source_bits_text, self.result_bits_text):
            widget.delete('1.0', tk.END)
        self.status_var.set("Поля вывода очищены.")

    def _process_file(self, operation_name: str):
        validated = self._validate_inputs()
        if validated is None:
            return
        state, input_path, output_path = validated

        try:
            lfsr = LFSR32(state)
            processed_bytes = 0
            display_source = bytearray()
            display_key = bytearray()
            display_result = bytearray()

            with open(input_path, 'rb') as source_file, open(output_path, 'wb') as result_file:
                while True:
                    chunk = source_file.read(self.FILE_CHUNK_SIZE)
                    if not chunk:
                        break

                    preview_count = max(0, min(self.DISPLAY_BYTE_LIMIT - len(display_source), len(chunk)))
                    result_chunk, key_preview = lfsr.xor_chunk(chunk, preview_count)
                    if preview_count:
                        display_source.extend(chunk[:preview_count])
                        display_key.extend(key_preview)
                        display_result.extend(result_chunk[:preview_count])
                    result_file.write(result_chunk)
                    processed_bytes += len(chunk)

            key_bits = bytes_to_bit_string(display_key)
            source_bits = bytes_to_bit_string(display_source)
            result_bits = bytes_to_bit_string(display_result)

            self.key_text.delete('1.0', tk.END)
            self.key_text.insert(tk.END, self._format_bits_for_display(key_bits))

            self.source_bits_text.delete('1.0', tk.END)
            self.source_bits_text.insert(tk.END, self._format_bits_for_display(source_bits))

            self.result_bits_text.delete('1.0', tk.END)
            self.result_bits_text.insert(tk.END, self._format_bits_for_display(result_bits))

            self.status_var.set(
                f"Операция '{operation_name}' выполнена. Обработано байт: {processed_bytes}. "
                f"В полях показаны первые {len(display_source)} байт. Файл сохранен: {output_path}"
            )
            messagebox.showinfo(
                "Готово",
                f"Операция '{operation_name}' успешно выполнена.\n"
                f"Обработано байт: {processed_bytes}\n"
                f"В полях показаны первые {len(display_source)} байт.\n"
                f"Результат сохранен в:\n{output_path}"
            )
        except Exception as e:
            messagebox.showerror("Ошибка", f"Не удалось выполнить операцию.\n{e}")

    @staticmethod
    def _format_bits_for_display(bit_string: str, group: int = 8, line_groups: int = 8) -> str:
        if not bit_string:
            return ""
        parts = [bit_string[i:i + group] for i in range(0, len(bit_string), group)]
        lines = []
        for i in range(0, len(parts), line_groups):
            lines.append(' '.join(parts[i:i + line_groups]))
        return '\n'.join(lines)

    def encrypt_file(self):
        self._process_file("шифрование")

    def decrypt_file(self):
        self._process_file("дешифрование")


if __name__ == '__main__':
    app = App()
    app.mainloop()
