import os
import subprocess
import re  # For splitting text into sentences or segments
import warnings
import tkinter as tk  # For creating GUI applications
from tkinter import ttk, filedialog, messagebox  # Additional tkinter widgets
import tkinter.font as tkfont  # For dynamic font scaling
import sounddevice as sd  # To capture audio input/output
import numpy as np  # For numerical operations (used for audio data)
import speech_recognition as sr  # For converting speech to text
from deep_translator import GoogleTranslator  # For performing translations using Google
import threading  # For running tasks concurrently in background threads
import queue  # For thread-safe communication between threads
from scipy.io.wavfile import write, read  # For saving/reading audio files
from pystray import Icon, Menu, MenuItem  # For creating a system tray icon and menu
from PIL import Image, ImageDraw, ImageTk  # For image processing and displaying images in the GUI
import asyncio  # For asynchronous operations, particularly with TTS
import string
import difflib  # For comparing text segments and removing overlaps
import io
import logging  # For logging messages and errors to a file
from concurrent.futures import ThreadPoolExecutor  # For managing a pool of background threads
import sys
from collections import OrderedDict  # For implementing an LRU cache for translations
import pycountry  # For mapping language codes to country names
import shutil

# Filter out specific warnings from EbookLib
warnings.filterwarnings("ignore", category=UserWarning, module="ebooklib.epub")
warnings.filterwarnings("ignore", category=FutureWarning, module="ebooklib.epub")
# Written by ChatGPT 01 and 03
#Tom Moir 1/3/2025
#tomspeechnz@gmail.com
# Import modules for reading EPUB files
from ebooklib import epub
from bs4 import BeautifulSoup

# On Windows, hide the console window when running a bundled executable
if os.name == "nt":
    CREATE_NO_WINDOW = 0x08000000
    original_popen = subprocess.Popen


    def no_window_popen(*args, **kwargs):
        if os.name == "nt":
            kwargs.setdefault("creationflags", CREATE_NO_WINDOW)
        return original_popen(*args, **kwargs)


    subprocess.Popen = no_window_popen

import edge_tts  # For Microsoft Edge Text-to-Speech
from pydub import AudioSegment  # For converting MP3 audio to WAV

# Set up logging to write debug/error messages to a file in the user's home directory
log_file = os.path.join(os.path.expanduser("~"), "translator_app_debug.log")
logging.basicConfig(
    level=logging.DEBUG,
    format='%(asctime)s - %(levelname)s - %(message)s',
    filename=log_file,
    filemode='a'
)


# Function to extract text from an EPUB file
def epub_to_text(epub_path):
    """
    Reads an EPUB file and returns the concatenated plain text.
    """
    try:
        book = epub.read_epub(epub_path)
        full_text = ""
        # Iterate over items and extract text from HTML content
        for item in book.get_items():
            if isinstance(item, epub.EpubHtml):
                soup = BeautifulSoup(item.get_content(), "html.parser")
                text = soup.get_text(separator="\n").strip()
                if text:
                    full_text += text + "\n\n"
        return full_text
    except Exception as e:
        logging.error(f"Error converting EPUB to text: {e}")
        return ""


# Function to merge segments that are too short to improve readability/translation
def merge_short_segments(segments, min_word_count=3, min_char_threshold=4):
    """
    Merges short text segments to avoid poor translation results.
    """
    segments = [s.strip() for s in segments if s.strip()]
    if not segments:
        return segments

    def is_too_short(seg):
        # Check if segment has fewer than the minimum word count
        if len(seg.split()) < min_word_count:
            return True
        # Also check if segment is a single short word
        token = seg.replace(".", "")
        if " " not in seg and token.isalpha() and len(token) <= min_char_threshold:
            return True
        return False

    merged = []
    for seg in segments:
        if is_too_short(seg):
            if merged:
                merged[-1] += " " + seg
            else:
                merged.append(seg)
        else:
            merged.append(seg)

    final = []
    i = 0
    while i < len(merged):
        seg = merged[i]
        if is_too_short(seg) and i + 1 < len(merged):
            new_seg = seg + " " + merged[i + 1]
            final.append(new_seg)
            i += 2
        else:
            final.append(seg)
            i += 1
    return final


# Function to split text into segments using punctuation as a delimiter
def split_text_with_fallback(text, fallback_word_count=300):
    """
    Splits text into segments based on punctuation. If a segment is too long,
    it is further split by word count.
    """
    raw_segments = re.split(r'(?<=[.!?])\s+', text)
    new_segments = []
    for seg in raw_segments:
        words = seg.split()
        if len(words) > fallback_word_count:
            for i in range(0, len(words), fallback_word_count):
                new_segments.append(" ".join(words[i:i + fallback_word_count]))
        else:
            new_segments.append(seg)
    return new_segments


# Function to split long text for TTS into chunks of a maximum length
def split_text_for_tts(text, max_len=2000):
    """
    Splits text into smaller chunks so that each chunk is at most max_len characters.
    """
    words = text.split()
    chunks = []
    current_chunk = ""
    for word in words:
        if current_chunk:
            if len(current_chunk) + len(word) + 1 > max_len:
                chunks.append(current_chunk)
                current_chunk = word
            else:
                current_chunk += " " + word
        else:
            current_chunk = word
    if current_chunk:
        chunks.append(current_chunk)
    return chunks


# Main TranslatorApp class encapsulating the entire application
class TranslatorApp:
    def __init__(self, root):
        """
        Initialize the TranslatorApp:
          - Sets up GUI components.
          - Initializes audio capture, speech recognition, TTS, and translation caching.
          - Configures various control variables.
        """
        self.root = root
        self.is_listening = False
        self.samplerate = 16000
        self.chunk_size = 2048
        self.buffered_chunks = []
        self.gain = 1.0
        self.languages_swapped = False
        self.message_queue = queue.Queue()
        self.translation_queue = queue.Queue()
        self.task_queue = queue.Queue()

        self.MAX_RECOGNIZED_LINES = 100
        self.MAX_TRANSLATED_LINES = 100

        # Initialize variables for Text-to-Speech and UI settings
        self.tts_enabled = tk.BooleanVar(value=False)
        self.voice_var = tk.StringVar(value="Loading voices...")
        self.font_size_var = tk.IntVar(value=20)
        self.tts_output_device_var = tk.StringVar(value="Default")
        self.mic_level_queue = queue.Queue()

        # Set up translation cache (LRU-style)
        self.translation_cache = OrderedDict()
        self.cache_lock = threading.Lock()
        self.cache_size = 1000

        # Variables to control text reading from input
        self.text_segments = []
        self.text_segment_index = 0
        self.text_reading_active = True
        self.last_spoken_text = ""
        self.input_listbox = None
        self.input_text_box = None

        self.current_tts_text = ""

        # Variables for managing TTS processing queues
        self.audio_tts_queue = queue.Queue()
        self.audio_tts_processing = False
        self.text_tts_queue = queue.Queue()
        self.text_tts_processing = False
        self.tts_input_source = "audio"  # Could be "audio" (from mic) or "text" (manual input)

        self.audio_tts_buffer = ""
        self.audio_tts_timer = None

        # Variables to control translation speed (via UI sliders)
        self.listbox_speed_var = tk.IntVar(value=5)
        self.textbox_speed_var = tk.IntVar(value=5)

        # TTS speech rate control (100% is normal speed)
        self.tts_rate_var = tk.DoubleVar(value=100)

        # Overlap percentage for audio segments
        self.overlap_percentage = tk.DoubleVar(value=4)

        # Calculate scaling factor based on screen dimensions
        screen_width = self.root.winfo_screenwidth()
        screen_height = self.root.winfo_screenheight()
        self.scale_factor = min(screen_width / 800, screen_height / 700) * 0.75

        self.design_width = 600
        self.design_height = 600
        self.root.tk.call('tk', 'scaling', self.scale_factor)

        # Set up fonts based on the scaling factor
        self.label_font = tkfont.Font(family="Arial", size=int(10.5 * self.scale_factor))
        self.dropdown_font = tkfont.Font(family="Arial", size=int(9 * self.scale_factor))
        self.button_font = tkfont.Font(family="Arial", size=int(10.5 * self.scale_factor))
        self.main_button_font = tkfont.Font(family="Arial", size=int(10.5 * self.scale_factor))
        self.text_font = tkfont.Font(family="Arial", size=int(10.5 * self.scale_factor))

        # Set minimum window size
        combobox_width = int(60 * self.scale_factor)
        self.root.minsize(combobox_width + 150, int(600 * self.scale_factor))

        # Load language dictionary for translations
        self.languages = self.get_language_dict()
        self.language_code_to_name = {code: name for name, code in self.languages.items()}
        self.current_spoken_language = self.languages.get("English (US)", "en")
        self.current_target_language = self.languages.get("English (US)", "en")

        self.buffer_size_var = tk.IntVar(value=100)
        self.buffer_size = self.buffer_size_var.get()

        # Configure FFmpeg for audio conversion
        self.configure_ffmpeg()
        # Build GUI widgets
        self.create_widgets()
        # List available audio devices for selection
        self.list_audio_devices()

        # Start periodic updates for various UI components and queues
        self.root.after(100, self.update_textbox)
        self.root.after(100, self.update_translation_box)
        self.root.after(100, self.process_mic_level_queue)

        self.audio_thread = None
        self.audio_stop_event = threading.Event()

        # Set up and start the asyncio loop for TTS in a separate thread
        self.tts_loop = asyncio.new_event_loop()
        self.tts_thread = threading.Thread(target=self.start_tts_loop, daemon=True)
        self.tts_thread.start()

        # Set up a thread pool for audio processing tasks
        self.executor = ThreadPoolExecutor(max_workers=2)
        # Load available TTS voices asynchronously
        self.list_edge_tts_voices()

        # Set up observers to update languages when UI selections change
        self.spoken_language_var.trace_add('write', self.update_spoken_language)
        self.target_language_var.trace_add('write', self.update_target_language)
        self.root.bind("<Configure>", self.on_resize)

        self.last_reported_language = None
        self.last_recognized_tail = ""

    # Called on window resize to adjust scaling and fonts dynamically
    def on_resize(self, event):
        if event.widget == self.root:
            new_scale = min(event.width / self.design_width, event.height / self.design_height)
            if abs(new_scale - self.scale_factor) > 0.01:
                self.scale_factor = new_scale
                self.root.tk.call('tk', 'scaling', self.scale_factor)
                self.label_font.configure(size=int(10.5 * self.scale_factor))
                self.dropdown_font.configure(size=int(9 * self.scale_factor))
                self.button_font.configure(size=int(10.5 * self.scale_factor))
                self.main_button_font.configure(size=int(10.5 * self.scale_factor))
                self.text_font.configure(size=int(10.5 * self.scale_factor))
                logging.debug(f"Dynamic resize: new scale factor set to {self.scale_factor}")
                if hasattr(self, "logo_label"):
                    self.logo_label.place_configure(relx=1.0, y=0, anchor="ne")

    # Start the asynchronous TTS loop in a background thread
    def start_tts_loop(self):
        asyncio.set_event_loop(self.tts_loop)
        try:
            self.tts_loop.run_forever()
        except Exception as e:
            self.add_message_to_queue(f"TTS event loop error: {e}\n")
            logging.error(f"TTS event loop error: {e}")

    # Stop the TTS loop gracefully
    def stop_tts_loop(self):
        try:
            self.tts_loop.call_soon_threadsafe(self.tts_loop.stop)
            self.tts_thread.join(timeout=5)
            logging.info("TTS event loop stopped successfully.")
        except Exception as e:
            logging.error(f"Error stopping TTS loop: {e}")

    # Configure FFmpeg path for audio conversion, especially in frozen executables
    def configure_ffmpeg(self):
        try:
            if getattr(sys, 'frozen', False):
                base_path = sys._MEIPASS
                ffmpeg_executable = 'ffmpeg.exe' if os.name == 'nt' else 'ffmpeg'
                ffmpeg_path = os.path.join(base_path, 'ffmpeg', 'bin', ffmpeg_executable)
                logging.debug(f"Looking for bundled ffmpeg at: {ffmpeg_path}")
                if os.path.isfile(ffmpeg_path):
                    AudioSegment.converter = ffmpeg_path
                    logging.debug(f"Bundled ffmpeg found at: {ffmpeg_path}")
                else:
                    logging.warning(f"Bundled ffmpeg not found at: {ffmpeg_path}. Using system ffmpeg if available.")
                    if shutil.which('ffmpeg'):
                        AudioSegment.converter = 'ffmpeg'
                    else:
                        error_message = "FFmpeg not found. Please install FFmpeg and ensure it's in the system PATH."
                        self.add_message_to_queue(error_message + "\n")
                        logging.error(error_message)
            else:
                logging.debug("Not running in a bundled executable. Using system ffmpeg.")
                if not shutil.which('ffmpeg'):
                    error_message = "FFmpeg not found. Please install FFmpeg and ensure it's in the system PATH."
                    self.add_message_to_queue(error_message + "\n")
                    logging.error(error_message)
        except Exception as e:
            self.add_message_to_queue(f"Error configuring ffmpeg: {e}\n")
            logging.error(f"Error configuring ffmpeg: {e}")

    # Create and arrange all main GUI widgets
    def create_widgets(self):
        self.root.title("Real-Time Language Translator")
        window_width = int(600 * self.scale_factor)
        window_height = int(600 * self.scale_factor)
        self.root.geometry(f"{window_width}x{window_height}")
        self.root.configure(bg="#f4f4f4")
        try:
            logo_original = Image.open("logo.jpg")
            logo_resized = logo_original.resize((150, 150), Image.LANCZOS)
            self.logo_image = ImageTk.PhotoImage(logo_resized)
            self.logo_label = tk.Label(self.root, image=self.logo_image, bg="#f4f4f4", bd=0)
            self.logo_label.place(relx=1.0, y=0, anchor="ne")
            self.logo_label.lift()
        except Exception as e:
            logging.error(f"Error loading logo: {e}")
            self.add_message_to_queue(f"Error loading logo: {e}\n")
            self.logo_label = tk.Label(self.root, text="", bg="#f4f4f4")
            self.logo_label.place(relx=1.0, y=0, anchor="ne")
        # Top frame for language and device selections
        top_frame = tk.Frame(self.root, bg="#e0e0e0", bd=2, relief="groove", padx=0, pady=int(7.5 * self.scale_factor))
        top_frame.pack(side=tk.TOP, fill="x")
        # Bottom frame for controls like audio capture and buffers
        bottom_frame = tk.Frame(self.root, bg="#e0e0e0", bd=2, relief="groove", padx=int(7.5 * self.scale_factor),
                                pady=int(7.5 * self.scale_factor))
        bottom_frame.pack(side=tk.BOTTOM, fill="x")
        # Frame for language selection dropdowns
        lang_frame = tk.Frame(top_frame, bg="#e0e0e0")
        lang_frame.pack(side=tk.TOP, anchor="w", fill="x", padx=0)
        spoken_language_label = tk.Label(lang_frame, text="Select Spoken Language:", bg="#e0e0e0", fg="black",
                                         font=self.label_font)
        spoken_language_label.pack(anchor="w")
        self.spoken_language_var = tk.StringVar(value="English (US)")
        spoken_language_dropdown = ttk.Combobox(lang_frame, textvariable=self.spoken_language_var,
                                                values=list(self.languages.keys()), state="readonly",
                                                font=self.dropdown_font)
        spoken_language_dropdown.pack(anchor="w", pady=(0, 5))
        target_language_label = tk.Label(lang_frame, text="Select Target Translation Language:", bg="#e0e0e0",
                                         fg="black", font=self.label_font)
        target_language_label.pack(anchor="w")
        self.target_language_var = tk.StringVar(value="English (US)")
        target_language_dropdown = ttk.Combobox(lang_frame, textvariable=self.target_language_var,
                                                values=list(self.languages.keys()), state="readonly",
                                                font=self.dropdown_font)
        target_language_dropdown.pack(anchor="w", pady=(0, 5))
        # Button to swap spoken and target languages
        self.swap_button = tk.Button(lang_frame, text="Swap Languages", command=self.swap_languages, bg="silver",
                                     fg="black", font=self.main_button_font, relief="raised", bd=4)
        self.swap_button.pack(anchor="w", pady=(0, 5))
        # Frame for microphone device selection
        device_frame = tk.Frame(top_frame, bg="#e0e0e0")
        device_frame.pack(side=tk.TOP, anchor="w", fill="x", padx=(60, 0), pady=(int(7.5 * self.scale_factor), 0))
        device_label = tk.Label(device_frame, text="Select Microphone Device:", bg="#e0e0e0", fg="black",
                                font=self.label_font)
        device_label.pack(anchor="w")
        self.device_combobox = ttk.Combobox(device_frame, state="readonly", font=self.dropdown_font, width=60)
        self.device_combobox.pack(anchor="w", pady=(0, int(3.75 * self.scale_factor)))
        # Progress bar to show microphone level
        self.mic_level = tk.DoubleVar()
        mic_progress = ttk.Progressbar(bottom_frame, orient="horizontal", mode="determinate",
                                       length=int(375 * self.scale_factor), variable=self.mic_level, maximum=100)
        mic_progress.pack(pady=int(7.5 * self.scale_factor))
        # Frame for various control buttons (start, flush, load file, enter text)
        button_frame = tk.Frame(bottom_frame, bg="#e0e0e0")
        button_frame.pack(pady=int(7.5 * self.scale_factor))
        self.start_button = tk.Button(button_frame, text="Start Audio Capture", command=self.toggle_recognition,
                                      bg="silver", fg="black", font=self.main_button_font, relief="raised", bd=4)
        self.start_button.pack(side=tk.LEFT, padx=5)
        flush_button = tk.Button(button_frame, text="Flush Buffers", command=self.flush_buffers, bg="silver",
                                 fg="black", font=self.main_button_font, relief="raised", bd=4)
        flush_button.pack(side=tk.LEFT, padx=5)
        read_file_button = tk.Button(button_frame, text="Read File", command=self.open_listbox_input_window,
                                     bg="silver", fg="black", font=self.main_button_font, relief="raised", bd=4)
        read_file_button.pack(side=tk.LEFT, padx=5)
        enter_text_button = tk.Button(button_frame, text="Enter Text", command=self.open_textbox_input_window,
                                      bg="silver", fg="black", font=self.main_button_font, relief="raised", bd=4)
        enter_text_button.pack(side=tk.LEFT, padx=5)
        # Slider to adjust microphone gain
        gain_slider = tk.Scale(bottom_frame, from_=1.0, to_=4.0, resolution=0.1, orient="horizontal", label="Mic Gain",
                               length=int(225 * self.scale_factor), command=self.set_gain, font=self.label_font)
        gain_slider.set(1.0)
        gain_slider.pack(pady=int(7.5 * self.scale_factor), anchor="w", padx=160)
        # Slider to adjust buffer size for audio capture
        buffer_size_frame = tk.Frame(bottom_frame, bg="#e0e0e0")
        buffer_size_frame.pack(pady=int(7.5 * self.scale_factor), anchor="w", padx=20)
        buffer_size_label = tk.Label(buffer_size_frame, text="Buffer Size:", bg="#e0e0e0", fg="black",
                                     font=self.label_font)
        buffer_size_label.pack(side=tk.LEFT, padx=(0, 10))
        self.buffer_size_slider = tk.Scale(buffer_size_frame, from_=20, to=140, resolution=10, orient="horizontal",
                                           variable=self.buffer_size_var, command=self.update_buffer_size,
                                           length=int(200 * self.scale_factor), font=self.dropdown_font)
        self.buffer_size_slider.pack(side=tk.LEFT)
        self.buffer_size_slider.set(100)
        # Slider to control overlap percentage between audio buffers
        overlap_frame = tk.Frame(bottom_frame, bg="#e0e0e0")
        overlap_frame.pack(pady=int(7.5 * self.scale_factor), anchor="w", padx=20)
        overlap_label = tk.Label(overlap_frame, text="Overlap (%):", bg="#e0e0e0", fg="black", font=self.label_font)
        overlap_label.pack(side=tk.LEFT, padx=(0, 10))
        self.overlap_slider = tk.Scale(overlap_frame, from_=0, to=20, resolution=1, orient="horizontal",
                                       variable=self.overlap_percentage, font=self.dropdown_font)
        self.overlap_slider.pack(side=tk.LEFT)
        # Text box to display recognized audio text
        self.output_window_text_box = tk.Text(self.root, height=int(15 * self.scale_factor),
                                              width=int(60 * self.scale_factor), bg="#ffffff", font=self.text_font,
                                              bd=3, relief="sunken")
        self.output_window_text_box.pack(side=tk.LEFT, padx=int(7.5 * self.scale_factor),
                                         pady=int(7.5 * self.scale_factor))
        # Frame for bottom control buttons (save transcript, exit, minimize)
        bottom_button_frame = tk.Frame(bottom_frame, bg="#e0e0e0")
        bottom_button_frame.pack(pady=int(7.5 * self.scale_factor))
        save_button = tk.Button(bottom_button_frame, text="Save Transcript", command=self.save_transcript, bg="silver",
                                fg="black", font=self.main_button_font, relief="raised", bd=4)
        save_button.pack(side=tk.LEFT, padx=5)
        exit_button = tk.Button(bottom_button_frame, text="Halt and Clean Exit", command=self.halt_and_exit,
                                bg="silver", fg="black", font=self.main_button_font, relief="raised", bd=4)
        exit_button.pack(side=tk.LEFT, padx=5)
        minimize_button = tk.Button(bottom_button_frame, text="Minimize to Tray", command=self.minimize_to_tray,
                                    bg="silver", fg="black", font=self.main_button_font, relief="raised", bd=4)
        minimize_button.pack(side=tk.LEFT, padx=5)
        # Create the translation window (separate Toplevel window)
        self.create_translation_window()
        self.logo_label.lift()

    # Opens a new window with a listbox to load text from a file
    def open_listbox_input_window(self):
        self.input_listbox = None
        self.input_text_box = None
        text_window = tk.Toplevel(self.root)
        text_window.title("Read File (Listbox)")
        text_window.geometry(f"{int(600 * self.scale_factor)}x{int(400 * self.scale_factor)}")
        text_window.configure(bg="#f4f4f4")
        main_frame = tk.Frame(text_window, bg="#f4f4f4")
        main_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        listbox_frame = tk.Frame(main_frame, bg="#f4f4f4")
        listbox_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        list_scrollbar = tk.Scrollbar(listbox_frame)
        list_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        self.input_listbox = tk.Listbox(listbox_frame, font=self.text_font, yscrollcommand=list_scrollbar.set)
        self.input_listbox.pack(fill=tk.BOTH, expand=True)
        list_scrollbar.config(command=self.input_listbox.yview)
        speed_slider = tk.Scale(listbox_frame, from_=1, to=10, orient="horizontal", variable=self.listbox_speed_var,
                                label="Translation Speed", font=self.text_font)
        speed_slider.pack(fill=tk.X, padx=5, pady=5)
        slider_frame = tk.Frame(main_frame, bg="#f4f4f4")
        slider_frame.pack(side=tk.RIGHT, fill=tk.Y, padx=5)
        self.jump_slider_value = tk.IntVar(value=1)
        self.jump_slider = tk.Scale(slider_frame, from_=1, to=1, orient="vertical", bg="#f4f4f4",
                                    variable=self.jump_slider_value, command=self.listbox_update_selection)
        self.jump_slider.pack(side=tk.LEFT, fill=tk.Y)
        self.jump_slider.bind("<ButtonPress-1>", lambda event: self.pause_text_reading())
        self.jump_slider.bind("<ButtonRelease-1>", lambda event: self.jump_via_listbox())
        self.vernier_slider = tk.Scale(slider_frame, from_=-9, to=9, orient="vertical", resolution=1, bg="#f4f4f4",
                                       length=int(150 * self.scale_factor))
        self.vernier_slider.set(0)
        self.vernier_slider.pack(side=tk.LEFT, fill=tk.Y, padx=(5, 0))
        self.vernier_slider.bind("<ButtonPress-1>", self.vernier_press)
        self.vernier_slider.bind("<B1-Motion>", self.vernier_motion)
        self.vernier_slider.bind("<ButtonRelease-1>", self.vernier_release)
        button_frame = tk.Frame(text_window, bg="#f4f4f4")
        button_frame.pack(pady=10, anchor="w")
        small_button_font = self.main_button_font
        load_file_button = tk.Button(button_frame, text="Load File", command=self.read_into_listbox, bg="silver",
                                     fg="black", font=small_button_font, relief="raised", bd=4)
        load_file_button.pack(side=tk.LEFT, padx=5)
        submit_button = tk.Button(button_frame, text="Begin", command=self.submit_listbox_input, bg="silver",
                                  fg="black", font=small_button_font, relief="raised", bd=4)
        submit_button.pack(side=tk.LEFT, padx=5)
        pause_button = tk.Button(button_frame, text="Pause Reading", command=self.pause_text_reading, bg="silver",
                                 fg="black", font=small_button_font, relief="raised", bd=4)
        pause_button.pack(side=tk.LEFT, padx=5)
        resume_button = tk.Button(button_frame, text="Resume Reading", command=self.resume_text_reading, bg="silver",
                                  fg="black", font=small_button_font, relief="raised", bd=4)
        resume_button.pack(side=tk.LEFT, padx=5)
        close_button = tk.Button(button_frame, text="Close", command=text_window.destroy, bg="silver", fg="black",
                                 font=small_button_font, relief="raised", bd=4)
        close_button.pack(side=tk.LEFT, padx=5)
        if self.input_listbox.size() > 0:
            self.text_segments = self.input_listbox.get(0, tk.END)
            self.jump_slider.config(from_=1, to=len(self.text_segments))
            self.jump_slider_value.set(1)

    # NEW: Opens a new window with a text box for manual text entry.
    def open_textbox_input_window(self):
        self.input_text_box = None
        self.input_listbox = None
        text_window = tk.Toplevel(self.root)
        text_window.title("Enter Text")
        text_window.geometry(f"{int(600 * self.scale_factor)}x{int(400 * self.scale_factor)}")
        text_window.configure(bg="#f4f4f4")
        main_frame = tk.Frame(text_window, bg="#f4f4f4")
        main_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        text_frame = tk.Frame(main_frame, bg="#f4f4f4")
        text_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar = tk.Scrollbar(text_frame)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        self.input_text_box = tk.Text(text_frame, height=15, width=40, font=self.text_font, bd=3, relief="sunken",
                                      yscrollcommand=scrollbar.set)
        self.input_text_box.pack(fill=tk.BOTH, expand=True)
        scrollbar.config(command=self.input_text_box.yview)
        speed_slider = tk.Scale(text_frame, from_=1, to=10, orient="horizontal", variable=self.textbox_speed_var,
                                label="Translation Speed", font=self.text_font)
        speed_slider.pack(fill=tk.X, padx=5, pady=5)
        slider_frame = tk.Frame(main_frame, bg="#f4f4f4")
        slider_frame.pack(side=tk.RIGHT, fill=tk.Y, padx=5)
        self.jump_slider_value = tk.IntVar(value=1)
        self.jump_slider = tk.Scale(slider_frame, from_=1, to=1, orient="vertical", bg="#f4f4f4",
                                    variable=self.jump_slider_value, command=self.update_highlight_position)
        self.jump_slider.pack(side=tk.LEFT, fill=tk.Y)
        self.jump_slider.bind("<ButtonPress-1>", lambda event: self.pause_text_reading())
        self.jump_slider.bind("<ButtonRelease-1>", lambda event: self.jump_via_textbox())
        self.vernier_slider = tk.Scale(slider_frame, from_=-9, to=9, orient="vertical", resolution=1, bg="#f4f4f4",
                                       length=int(150 * self.scale_factor))
        self.vernier_slider.set(0)
        self.vernier_slider.pack(side=tk.LEFT, fill=tk.Y, padx=(5, 0))
        self.vernier_slider.bind("<ButtonPress-1>", self.vernier_press)
        self.vernier_slider.bind("<B1-Motion>", self.vernier_motion)
        self.vernier_slider.bind("<ButtonRelease-1>", self.vernier_release_textbox)
        button_frame = tk.Frame(text_window, bg="#f4f4f4")
        button_frame.pack(pady=10, anchor="w")
        small_button_font = self.main_button_font
        submit_button = tk.Button(button_frame, text="Submit",
                                  command=lambda: self.submit_text_input(self.input_text_box), bg="silver", fg="black",
                                  font=small_button_font, relief="raised", bd=4)
        submit_button.pack(side=tk.LEFT, padx=5)
        pause_button = tk.Button(button_frame, text="Pause Reading", command=self.pause_text_reading, bg="silver",
                                 fg="black", font=small_button_font, relief="raised", bd=4)
        pause_button.pack(side=tk.LEFT, padx=5)
        resume_button = tk.Button(button_frame, text="Resume Reading", command=self.resume_text_reading, bg="silver",
                                  fg="black", font=small_button_font, relief="raised", bd=4)
        resume_button.pack(side=tk.LEFT, padx=5)
        paste_button = tk.Button(button_frame, text="Paste",
                                 command=lambda: self.input_text_box.insert(tk.INSERT, self.root.clipboard_get()),
                                 bg="silver", fg="black", font=small_button_font, relief="raised", bd=4)
        paste_button.pack(side=tk.LEFT, padx=5)
        close_button = tk.Button(button_frame, text="Close", command=text_window.destroy, bg="silver", fg="black",
                                 font=small_button_font, relief="raised", bd=4)
        close_button.pack(side=tk.LEFT, padx=5)
        # Bind the mouse click event to process a selection translation
        self.input_text_box.bind("<ButtonRelease-1>", self.on_text_click)

    # NEW: read_into_listbox method (restored from your original design)
    def read_into_listbox(self):
        file_path = filedialog.askopenfilename(
            title="Select a file",
            filetypes=[("Text files", "*.txt"), ("EPUB files", "*.epub")]
        )
        if not file_path:
            return
        try:
            if file_path.lower().endswith(".epub"):
                full_text = epub_to_text(file_path)
            else:
                with open(file_path, "r", encoding="utf-8") as f:
                    full_text = f.read()
            raw_segments = split_text_with_fallback(full_text, fallback_word_count=300)
            self.text_segments = merge_short_segments(raw_segments, min_word_count=3, min_char_threshold=4)
            self.input_listbox.delete(0, tk.END)
            for seg in self.text_segments:
                self.input_listbox.insert(tk.END, seg)
            if self.text_segments:
                self.jump_slider.config(from_=1, to=len(self.text_segments))
                self.jump_slider_value.set(1)
        except Exception as e:
            messagebox.showerror("File Read Error", f"Error reading file: {e}")

    # on_text_click: When text reading is paused, process a mouse click to get the selected text,
    # highlight it in yellow, translate it, insert the translation, and trigger TTS if enabled.
    def on_text_click(self, event):
        # Process only if text reading is paused.
        if not self.text_reading_active:
            try:
                start = self.input_text_box.index(tk.SEL_FIRST)
                end = self.input_text_box.index(tk.SEL_LAST)
                selected_text = self.input_text_box.get(tk.SEL_FIRST, tk.SEL_LAST)
            except tk.TclError:
                # No text is selected
                return

            # Remove any existing highlight and then highlight the selected text in yellow
            self.input_text_box.tag_remove("highlight", "1.0", tk.END)
            self.input_text_box.tag_add("highlight", start, end)
            self.input_text_box.tag_config("highlight", background="yellow")

            # Translate the selected text
            translation = self.translate_text(selected_text, self.current_target_language)
            if translation:
                # Insert the translation into the translated output box
                self.translated_text_box.insert(tk.END, f"\n[Selected Translation]: {translation}\n")
                # If TTS is enabled, trigger TTS for the translation
                if self.tts_enabled.get():
                    self.speak_text(translation, origin="text")
                # Optionally update the vertical slider based on the clicked line number
                line_number = int(start.split('.')[0])
                self.jump_slider_value.set(line_number)
        else:
            self.add_message_to_queue("Pause reading before selecting text for translation.\n")

    # Updates selection in the listbox based on a slider value
    def listbox_update_selection(self, value):
        try:
            idx = int(value) - 1
            if 0 <= idx < self.input_listbox.size():
                self.input_listbox.selection_clear(0, tk.END)
                self.input_listbox.selection_set(idx)
                self.input_listbox.see(idx)
        except Exception as e:
            logging.error(f"Error updating listbox selection: {e}")

    # Called when the vernier slider is pressed (pauses text reading)
    def vernier_press(self, event):
        self.pause_text_reading()

    # Called when the vernier slider is moved to adjust the current selection
    def vernier_motion(self, event):
        try:
            offset = int(self.vernier_slider.get())
            current = int(self.jump_slider_value.get())
            master_from = int(self.jump_slider.cget("from"))
            master_to = int(self.jump_slider.cget("to"))
            temp_value = max(master_from, min(current + offset, master_to))
            if self.input_listbox:
                self.listbox_update_selection(str(temp_value))
            elif self.input_text_box:
                self.update_highlight_position(str(temp_value))
        except Exception as e:
            logging.error(f"Error during vernier motion: {e}")

    # Called when the vernier slider is released in listbox mode
    def vernier_release(self, event):
        try:
            offset = int(self.vernier_slider.get())
            current = int(self.jump_slider_value.get())
            master_from = int(self.jump_slider.cget("from"))
            master_to = int(self.jump_slider.cget("to"))
            new_value = max(master_from, min(current + offset, master_to))
            self.jump_slider_value.set(new_value)
            self.jump_via_listbox()
        finally:
            self.vernier_slider.set(0)
            self.resume_text_reading()

    # Called when the vernier slider is released in textbox mode
    def vernier_release_textbox(self, event):
        try:
            offset = int(self.vernier_slider.get())
            current = int(self.jump_slider_value.get())
            master_from = int(self.jump_slider.cget("from"))
            master_to = int(self.jump_slider.cget("to"))
            new_value = max(master_from, min(current + offset, master_to))
            self.jump_slider_value.set(new_value)
            self.jump_via_textbox()
        finally:
            self.vernier_slider.set(0)
            self.resume_text_reading()

    # Highlights the currently selected segment in the input textbox
    def update_highlight_position(self, value):
        if not self.text_segments or not self.input_text_box:
            return
        try:
            new_index = int(value) - 1
            if new_index < 0 or new_index >= len(self.text_segments):
                return
            cumulative_chars = sum(len(s) for s in self.text_segments[:new_index])
            start_index = "1.0+" + str(cumulative_chars) + " chars"
            end_index = "1.0+" + str(cumulative_chars + len(self.text_segments[new_index])) + " chars"
            self.input_text_box.tag_remove("current", "1.0", tk.END)
            self.input_text_box.tag_add("current", start_index, end_index)
            self.input_text_box.tag_config("current", background="yellow")
            self.input_text_box.see(start_index)
            self.root.after(50, lambda: self.input_text_box.see(end_index))
        except Exception as e:
            logging.error(f"Error in update_highlight_position: {e}")

    # Jump to a selected segment from the listbox
    def jump_via_listbox(self):
        if not self.text_segments:
            messagebox.showinfo("No Text", "No text has been loaded yet.")
            return
        new_index = int(self.jump_slider_value.get()) - 1
        if new_index < len(self.text_segments):
            self.text_segment_index = new_index
            self.text_reading_active = True
            self.input_listbox.selection_clear(0, tk.END)
            self.input_listbox.selection_set(new_index)
            self.input_listbox.see(new_index)
            self.add_message_to_queue(f"Jumping to segment {new_index + 1}.\n")
            logging.info(f"Jumping to segment {new_index + 1}.")
            self.current_tts_text = ""
            self.process_next_text_segment()

    # Jump to a selected segment from the textbox
    def jump_via_textbox(self):
        if not self.text_segments:
            messagebox.showinfo("No Text", "No text has been loaded yet.")
            return
        new_index = int(self.jump_slider_value.get()) - 1
        if new_index < len(self.text_segments):
            self.text_segment_index = new_index
            self.text_reading_active = True
            self.input_text_box.tag_remove("current", "1.0", tk.END)
            cumulative_chars = sum(len(s) for s in self.text_segments[:new_index])
            start_index = "1.0+" + str(cumulative_chars) + " chars"
            end_index = "1.0+" + str(cumulative_chars + len(self.text_segments[new_index])) + " chars"
            self.input_text_box.tag_add("current", start_index, end_index)
            self.input_text_box.tag_config("current", background="yellow")
            self.input_text_box.see(start_index)
            self.add_message_to_queue(f"Jumping to segment {new_index + 1}.\n")
            logging.info(f"Jumping to segment {new_index + 1}.")
            self.current_tts_text = ""
            self.process_next_text_segment()

    # Submit text from the input textbox for translation
    def submit_text_input(self, input_widget):
        text = input_widget.get("1.0", tk.END).strip()
        if not text:
            messagebox.showwarning("No Text", "Please enter some text before submitting.")
            return
        self.tts_input_source = "text"
        raw_segments = split_text_with_fallback(text, fallback_word_count=300)
        self.text_segments = merge_short_segments(raw_segments, min_word_count=3, min_char_threshold=4)
        self.add_message_to_queue(f"Text Input ({self.spoken_language_var.get()}): {text}\n")
        self.translated_text_box.delete("1.0", tk.END)
        with self.cache_lock:
            self.translation_cache.clear()
        self.text_segment_index = 0
        self.text_reading_active = True
        if self.jump_slider:
            self.jump_slider.config(from_=1, to=len(self.text_segments))
            self.jump_slider_value.set(1)
        if self.input_listbox is not None:
            self.input_listbox.delete(0, tk.END)
            for segment in self.text_segments:
                self.input_listbox.insert(tk.END, segment)
        self.current_tts_text = ""
        self.process_next_text_segment()

    # Submit text from the listbox for translation
    def submit_listbox_input(self):
        items = self.input_listbox.get(0, tk.END)
        text = "\n".join(items)
        if not text.strip():
            messagebox.showwarning("No Text", "Please enter some text before submitting.")
            return
        self.tts_input_source = "text"
        self.handle_text_input(text)

    # Handle text input by setting up segments and clearing caches, then start processing
    def handle_text_input(self, text):
        self.add_message_to_queue(f"Text Input ({self.spoken_language_var.get()}): {text}\n")
        self.translated_text_box.delete("1.0", tk.END)
        with self.cache_lock:
            self.translation_cache.clear()
        raw_segments = split_text_with_fallback(text, fallback_word_count=300)
        self.text_segments = merge_short_segments(raw_segments, min_word_count=3, min_char_threshold=4)
        self.text_segment_index = 0
        self.text_reading_active = True
        if self.jump_slider:
            self.jump_slider.config(from_=1, to=len(self.text_segments))
            self.jump_slider_value.set(1)
        if self.input_listbox is not None:
            self.input_listbox.delete(0, tk.END)
            for segment in self.text_segments:
                self.input_listbox.insert(tk.END, segment)
        self.current_tts_text = ""
        self.process_next_text_segment()

    # Process the next segment of text for translation and TTS
    def process_next_text_segment(self):
        if not self.text_reading_active:
            return
        if self.text_segment_index >= len(self.text_segments):
            return
        segment = self.text_segments[self.text_segment_index].strip().replace("\n", " ")
        if hasattr(self, "jump_slider_value"):
            self.jump_slider_value.set(self.text_segment_index + 1)
        self.text_segment_index += 1
        if self.input_listbox is not None:
            self.input_listbox.selection_clear(0, tk.END)
            self.input_listbox.selection_set(self.text_segment_index - 1)
            self.input_listbox.see(self.text_segment_index - 1)
        elif self.input_text_box is not None:
            cumulative_chars = sum(len(s) for s in self.text_segments[:self.text_segment_index - 1])
            start_index = "1.0+" + str(cumulative_chars) + " chars"
            end_index = "1.0+" + str(cumulative_chars + len(self.text_segments[self.text_segment_index - 1])) + " chars"
            self.input_text_box.tag_remove("current", "1.0", tk.END)
            self.input_text_box.tag_add("current", start_index, end_index)
            self.input_text_box.tag_config("current", background="yellow")
            self.input_text_box.see(start_index)
        if not segment:
            self.root.after(10, self.process_next_text_segment)
            return
        # Translate only if spoken and target languages differ; otherwise, keep original text.
        if self.map_language_for_translation(self.current_target_language) != self.map_language_for_translation(
                self.current_spoken_language):
            translated_segment = self.translate_text(segment, self.current_target_language)
        else:
            translated_segment = segment
        self.add_translation_to_queue(f"{translated_segment}\n")
        self.current_tts_text = translated_segment
        word_count = len(segment.split())
        base_delay = max(1000, int(word_count * 500))
        if self.input_listbox is not None:
            slider_value = self.listbox_speed_var.get()
        elif self.input_text_box is not None:
            slider_value = self.textbox_speed_var.get()
        else:
            slider_value = 5
        multiplier = (11 - slider_value) / 5
        delay = int(base_delay * multiplier)
        self.root.after(delay, self.process_next_text_segment)

    # Pause the reading/translation of text segments
    def pause_text_reading(self):
        self.text_reading_active = False
        self.add_message_to_queue("Text reading paused.\n")
        logging.info("Text reading paused by user.")

    # Resume the reading/translation of text segments
    def resume_text_reading(self):
        if not self.text_reading_active:
            self.text_reading_active = True
            self.add_message_to_queue("Text reading resumed.\n")
            logging.info("Text reading resumed by user.")
            self.process_next_text_segment()

    # Flush all message and translation queues and clear audio buffers
    def flush_buffers(self):
        try:
            self.buffered_chunks.clear()
            while not self.message_queue.empty():
                self.message_queue.get_nowait()
            while not self.translation_queue.empty():
                self.translation_queue.get_nowait()
            while not self.mic_level_queue.empty():
                self.mic_level_queue.get_nowait()
            self.add_message_to_queue("Buffers flushed.\n")
            logging.info("Buffers flushed by user.")
        except Exception as e:
            self.add_message_to_queue(f"Error flushing buffers: {e}\n")
            logging.error(f"Error flushing buffers: {e}")

    # Translate a single text segment, using cache if available
    def _translate_single(self, text, target_language):
        cache_key = (text.lower(), target_language)
        with self.cache_lock:
            if cache_key in self.translation_cache:
                self.translation_cache.move_to_end(cache_key)
                return self.translation_cache[cache_key]
        try:
            target_language_mapped = self.map_language_for_translation(target_language)
            source_language_mapped = self.map_language_for_translation(self.current_spoken_language)
            translator = GoogleTranslator(source=source_language_mapped, target=target_language_mapped)
            translated = translator.translate(text)
            with self.cache_lock:
                self.translation_cache[cache_key] = translated
                if len(self.translation_cache) > self.cache_size:
                    oldest = next(iter(self.translation_cache))
                    del self.translation_cache[oldest]
            return translated
        except Exception as e:
            self.add_translation_to_queue(f"Translation failed: {e}\n")
            logging.error(f"Translation failed: {e}")
            return None

    # Translate text; if too long, split into smaller chunks
    def translate_text(self, text, target_language):
        max_length = 5000
        if not text.strip():
            return text
        if len(text) <= max_length:
            return self._translate_single(text, target_language)
        segments = split_text_with_fallback(text, fallback_word_count=300)
        final_segments = []
        for seg in segments:
            if len(seg) <= max_length:
                final_segments.append(seg)
            else:
                words = seg.split()
                current_chunk = ""
                for word in words:
                    if current_chunk:
                        if len(current_chunk) + len(word) + 1 > max_length:
                            final_segments.append(current_chunk)
                            current_chunk = word
                        else:
                            current_chunk += " " + word
                    else:
                        current_chunk = word
                if current_chunk:
                    final_segments.append(current_chunk)
        translated_segments = []
        for chunk in final_segments:
            translated_chunk = self._translate_single(chunk, target_language)
            if translated_chunk is not None:
                translated_segments.append(translated_chunk)
        return " ".join(translated_segments)

    # Map locale code to a country name (if applicable)
    def get_country_name_from_locale(self, locale_code):
        if locale_code.lower() == "cy-gb":
            return "Wales"
        if '-' in locale_code:
            parts = locale_code.split('-')
            if len(parts) >= 2:
                country_code = parts[1].upper()
                country = pycountry.countries.get(alpha_2=country_code)
                if country:
                    return country.name
        return ""

    # Get the full language name based on the locale code
    def get_full_language_name(self, locale_code):
        try:
            if '-' in locale_code:
                language_part, _ = locale_code.split('-')
            else:
                language_part = locale_code
            language = pycountry.languages.get(alpha_2=language_part)
            if language and hasattr(language, 'name'):
                language_name = language.name
            else:
                language_name = locale_code
            if language_name.lower() == "modern greek":
                language_name = "Greek Modern"
            return language_name
        except Exception:
            return locale_code

    # Highlight the currently translated sentence in the output text box
    def highlight_current_output_sentence(self, sentence):
        self.translated_text_box.tag_remove("current_output", "1.0", tk.END)
        index = self.translated_text_box.search(sentence, "1.0", tk.END)
        if index:
            end_index = f"{index}+{len(sentence)}c"
            self.translated_text_box.tag_add("current_output", index, end_index)
            self.translated_text_box.tag_config("current_output", background="yellow")
            logging.debug(f"Highlighted sentence from {index} to {end_index}.")

    # Update buffer size based on slider input
    def update_buffer_size(self, value):
        try:
            buffer_size = int(value)
            if 20 <= buffer_size <= 140:
                self.buffer_size = buffer_size
                self.add_message_to_queue(f"Buffer size set to: {buffer_size}\n")
                logging.info(f"Buffer size updated to: {buffer_size}")
            else:
                self.add_message_to_queue("Buffer size must be between 20 and 140.\n")
                logging.warning("Attempted to set buffer size outside allowed range.")
        except ValueError:
            self.add_message_to_queue("Invalid buffer size value.\n")
            logging.error("Invalid buffer size value entered.")

    # Create the translation window (separate from the main window)
    def create_translation_window(self):
        translation_window = tk.Toplevel(self.root)
        translation_window.title("Translation Window")
        translation_window.geometry(f"{int(700 * self.scale_factor)}x{int(600 * self.scale_factor)}")
        translation_window.configure(bg="#f4f4f4")
        translation_window.columnconfigure(0, weight=1)
        translation_window.rowconfigure(0, weight=1)
        text_frame = tk.Frame(translation_window, bg="#f4f4f4")
        text_frame.grid(row=0, column=0, sticky="nsew", padx=int(10 * self.scale_factor),
                        pady=int(10 * self.scale_factor))
        self.translated_text_box = tk.Text(text_frame, height=int(15 * self.scale_factor),
                                           width=int(80 * self.scale_factor), bg="#ffffff",
                                           font=("Arial", self.font_size_var.get()), bd=3, relief="sunken")
        self.translated_text_box.pack(fill="both", expand=True)
        controls_frame = tk.Frame(translation_window, bg="#f4f4f4")
        controls_frame.grid(row=1, column=0, sticky="ew", padx=int(10 * self.scale_factor),
                            pady=int(10 * self.scale_factor))
        tts_check = tk.Checkbutton(controls_frame, text="Enable Text-to-Speech", variable=self.tts_enabled,
                                   bg="#f4f4f4", fg="black", font=self.button_font, command=self.toggle_tts)
        tts_check.grid(row=0, column=0, pady=(10, 5), sticky="w")
        tts_device_label = tk.Label(controls_frame, text="Select TTS Output Device:", bg="#f4f4f4", fg="black",
                                    font=self.label_font)
        tts_device_label.grid(row=0, column=1, padx=(10, 0), pady=(10, 5), sticky="w")
        self.tts_output_device_combobox = ttk.Combobox(controls_frame, textvariable=self.tts_output_device_var,
                                                       values=self.get_output_devices(), state="readonly",
                                                       font=self.dropdown_font, width=30)
        self.tts_output_device_combobox.grid(row=0, column=2, padx=(10, 0), pady=(10, 5), sticky="w")
        self.tts_output_device_combobox.set("Default")
        options_frame = tk.Frame(translation_window, bg="#f4f4f4")
        options_frame.grid(row=2, column=0, sticky="ew", padx=int(10 * self.scale_factor), pady=(5, 10))
        voice_frame = tk.Frame(options_frame, bg="#f4f4f4")
        voice_frame.grid(row=0, column=0, padx=(0, 20), pady=5, sticky="w")
        voice_label = tk.Label(voice_frame, text="Select Voice:", bg="#f4f4f4", fg="black", font=self.label_font)
        voice_label.pack(side=tk.LEFT, padx=(0, 10))
        self.voice_combobox = ttk.Combobox(voice_frame, textvariable=self.voice_var, values=["Loading voices..."],
                                           state="disabled", font=self.dropdown_font, width=50)
        self.voice_combobox.pack(side=tk.LEFT)
        font_size_frame = tk.Frame(translation_window, bg="#f4f4f4")
        font_size_frame.grid(row=3, column=0, sticky="ew", padx=int(10 * self.scale_factor), pady=(5, 10))
        font_size_label = tk.Label(font_size_frame, text="Translated Text Font Size:", bg="#f4f4f4", fg="black",
                                   font=self.label_font)
        font_size_label.pack(side=tk.LEFT, padx=(0, 10))
        font_size_slider = tk.Scale(font_size_frame, from_=10, to=40, orient="horizontal",
                                    length=int(200 * self.scale_factor), variable=self.font_size_var,
                                    command=self.set_translation_font_size, font=self.dropdown_font)
        font_size_slider.set(20)
        font_size_slider.pack(side=tk.LEFT, padx=(10, 0), pady=5)
        tts_rate_frame = tk.Frame(translation_window, bg="#f4f4f4")
        tts_rate_frame.grid(row=4, column=0, sticky="ew", padx=int(10 * self.scale_factor), pady=(5, 10))
        tts_rate_label = tk.Label(tts_rate_frame, text="TTS Speech Rate (%):", bg="#f4f4f4", fg="black",
                                  font=self.label_font)
        tts_rate_label.pack(side=tk.LEFT, padx=(0, 10))
        tts_rate_slider = tk.Scale(tts_rate_frame, from_=50, to=150, orient="horizontal", variable=self.tts_rate_var,
                                   resolution=1, font=self.dropdown_font)
        tts_rate_slider.set(100)
        tts_rate_slider.pack(side=tk.LEFT, padx=(10, 0), pady=5)
        # Batch translation button starts background processing with a progress indicator.
        batch_translate_button = tk.Button(translation_window, text="Batch Tran",
                                           command=self.batch_translate_document,
                                           bg="silver", fg="black", font=self.main_button_font,
                                           relief="raised", bd=4)
        batch_translate_button.place(relx=0.95, rely=0.85, anchor="se")
        save_output_button = tk.Button(translation_window, text="Save Output", command=self.save_translation_output,
                                       bg="silver", fg="black", font=self.main_button_font, relief="raised", bd=4)
        save_output_button.place(relx=0.95, rely=0.95, anchor="se")
        clear_button = tk.Button(translation_window, text="Clear Screen", command=self.clear_translated_text,
                                 bg="silver", fg="black", font=self.main_button_font, relief="raised", bd=4)
        clear_button.place(relx=0.7, rely=0.95, anchor="s")

    # Clear the translated text output box
    def clear_translated_text(self):
        self.translated_text_box.delete("1.0", tk.END)
        self.add_message_to_queue("Translation output cleared.\n")

    # Save the transcript (both recognized text and translated text) to a file
    def save_translation_output(self):
        output_text = self.translated_text_box.get("1.0", tk.END).strip()
        if not output_text:
            messagebox.showwarning("No Text", "There is no text output to save.")
            return
        file_path = filedialog.asksaveasfilename(defaultextension=".txt", filetypes=[("Text files", "*.txt")],
                                                 title="Save Translation Output")
        if file_path:
            try:
                with open(file_path, "w", encoding="utf-8") as f:
                    f.write(output_text)
                messagebox.showinfo("Saved", f"Translation output saved to:\n{file_path}")
            except Exception as e:
                messagebox.showerror("Error", f"Error saving translation output: {e}")

    # Adjust the font size of the translated text box based on slider value
    def set_translation_font_size(self, size):
        try:
            new_font = ("Arial", int(size))
            self.translated_text_box.config(font=new_font)
            logging.info(f"Translated text font size set to: {size}")
        except ValueError:
            self.add_message_to_queue("Invalid font size selected.\n")
            logging.error("Invalid font size selected.")

    # Swap the spoken and target language selections
    def swap_languages(self):
        try:
            if self.spoken_language_var.get() == self.target_language_var.get():
                messagebox.showinfo("Swap Languages", "Spoken and target languages are the same. Swap not required.")
                logging.info("Attempted to swap languages, but both languages are the same.")
                return
            original_spoken = self.spoken_language_var.get()
            self.spoken_language_var.set(self.target_language_var.get())
            self.target_language_var.set(original_spoken)
            self.swap_button.config(text="Swap Languages", bg="silver", fg="black")
            logging.info("Languages swapped: Spoken and target languages exchanged.")
        except Exception as e:
            self.add_message_to_queue(f"Error swapping languages: {e}\n")
            logging.error(f"Error swapping languages: {e}")

    # List available audio input devices and load them into the combobox
    def list_audio_devices(self):
        try:
            devices = sd.query_devices()
            hostapis = sd.query_hostapis()
            device_list = []
            for i, device in enumerate(devices):
                if device['max_input_channels'] > 0:
                    hostapi = hostapis[device['hostapi']]
                    wasapi_prefix = ""
                    if "wasapi" in hostapi['name'].lower():
                        wasapi_prefix = "WASAPI "
                    device_list.append(
                        f"{i}: {wasapi_prefix}{device['name']} (Input Channels: {device['max_input_channels']})")
            self.device_combobox['values'] = device_list
            if device_list:
                self.device_combobox.current(0)
                self.add_message_to_queue("Microphone devices loaded into the menu.\n")
                logging.info("Microphone devices loaded successfully.")
            else:
                self.add_message_to_queue("No input devices found.\n")
                logging.warning("No input devices found.")
        except Exception as e:
            self.add_message_to_queue(f"Error listing audio devices: {e}\n")
            logging.error(f"Error listing audio devices: {e}")

    # Halt audio capture, stop TTS, and cleanly exit the program
    def halt_and_exit(self):
        try:
            if self.is_listening:
                self.toggle_recognition()
                logging.info("Stopped audio capture before exiting.")
            self.stop_tts_loop()
            if hasattr(self, 'tray_icon') and self.tray_icon:
                self.tray_icon.stop()
                logging.info("System tray icon stopped.")
            self.executor.shutdown(wait=True)
            logging.info("ThreadPoolExecutor shutdown.")
            self.root.quit()
            self.root.destroy()
            logging.info("Application halted and exited.")
            sys.exit()
        except Exception as e:
            self.add_message_to_queue(f"Error during shutdown: {e}\n")
            logging.error(f"Error during shutdown: {e}")
            sys.exit()

    # Minimize the application to the system tray
    def minimize_to_tray(self):
        try:
            icon_image = Image.open("icon.ico")
            icon_image = icon_image.resize((64, 64))
            menu = Menu(MenuItem('Restore', self.restore_from_tray), MenuItem('Exit', self.halt_and_exit))
            self.tray_icon = Icon("TranslatorApp", icon_image, "Translator", menu)
            self.root.withdraw()
            logging.info("Application minimized to system tray.")
            threading.Thread(target=self.tray_icon.run, daemon=True).start()
        except Exception as e:
            self.add_message_to_queue(f"Error minimizing to tray: {e}\n")
            logging.error(f"Error minimizing to tray: {e}")

    # Restore the application from the system tray
    def restore_from_tray(self, icon, item):
        try:
            self.tray_icon.stop()
            self.root.deiconify()
            logging.info("Application restored from system tray.")
        except Exception as e:
            self.add_message_to_queue(f"Error restoring from tray: {e}\n")
            logging.error(f"Error restoring from tray: {e}")

    # Return a dictionary mapping language names to their codes
    def get_language_dict(self):
        return {
            "Afrikaans": "af", "Albanian": "sq", "Amharic": "am", "Arabic": "ar", "Armenian": "hy", "Azerbaijani": "az",
            "Basque": "eu", "Belarusian": "be", "Bengali": "bn", "Bosnian": "bs", "Bulgarian": "bg", "Catalan": "ca",
            "Cebuano": "ceb", "Chichewa": "ny", "Chinese (Simplified)": "zh-CN", "Chinese (Traditional)": "zh-TW",
            "Corsican": "co", "Croatian": "hr", "Czech": "cs", "Danish": "da", "Dutch": "nl", "English (US)": "en-US",
            "English (UK)": "en-GB", "Esperanto": "eo", "Estonian": "et", "Filipino": "tl", "Finnish": "fi",
            "French": "fr", "Frisian": "fy", "Galician": "gl", "Georgian": "ka", "German": "de", "Greek Modern": "el",
            "Gujarati": "gu", "Haitian Creole": "ht", "Hausa": "ha", "Hebrew": "iw", "Hindi": "hi", "Hmong": "hmn",
            "Hungarian": "hu", "Icelandic": "is", "Igbo": "ig", "Indonesian": "id", "Irish": "ga", "Italian": "it",
            "Japanese": "ja", "Javanese": "jw", "Kannada": "kn", "Kazakh": "kk", "Khmer": "km", "Kinyarwanda": "rw",
            "Korean": "ko", "Kurdish (Kurmanji)": "ku", "Kyrgyz": "ky", "Lao": "lo", "Latin": "la", "Latvian": "lv",
            "Lithuanian": "lt", "Luxembourgish": "lb", "Macedonian": "mk", "Malagasy": "mg", "Malay": "ms",
            "Malayalam": "ml",
            "Maltese": "mt", "Maori": "mi", "Marathi": "mr", "Mongolian": "mn", "Myanmar": "my", "Nepali": "ne",
            "Norwegian": "no", "Odia": "or", "Pashto": "ps", "Persian": "fa", "Polish": "pl", "Portuguese": "pt",
            "Punjabi": "pa", "Romanian": "ro", "Russian": "ru", "Samoan": "sm", "Scots Gaelic": "gd", "Serbian": "sr",
            "Sesotho": "st", "Shona": "sn", "Sindhi": "sd", "Sinhala": "si", "Slovak": "sk", "Slovenian": "sl",
            "Somali": "so", "Spanish": "es", "Sundanese": "su", "Swahili": "sw", "Swedish": "sv", "Tajik": "tg",
            "Tamil": "ta", "Tatar": "tt", "Telugu": "te", "Thai": "th", "Turkish": "tr", "Turkmen": "tk",
            "Ukrainian": "uk", "Urdu": "ur", "Uyghur": "ug", "Uzbek": "uz", "Vietnamese": "vi", "Welsh": "cy",
            "Xhosa": "xh", "Yiddish": "yi", "Yoruba": "yo", "Zulu": "zu"
        }

    # Adds a message to the general message queue for display
    def add_message_to_queue(self, message):
        self.message_queue.put(message)
        logging.debug(message.strip())

    # Adds a message to the translation message queue for display
    def add_translation_to_queue(self, message):
        self.translation_queue.put(message)
        logging.debug(f"Translation added to queue: {message.strip()}")

    # Inserts text into a widget while maintaining a maximum number of lines
    def insert_text_with_limit(self, text_widget, message, max_lines):
        text_widget.insert(tk.END, message)
        text_widget.yview_moveto(1.0)
        current_lines = int(text_widget.index('end-1c').split('.')[0])
        if current_lines > max_lines:
            lines_to_delete = current_lines - max_lines
            text_widget.delete("1.0", f"{lines_to_delete + 1}.0")
            logging.debug(f"Deleted {lines_to_delete} lines from the text box to maintain max lines.")

    # Periodically update the output text box with messages from the queue
    def update_textbox(self):
        try:
            while not self.message_queue.empty():
                message = self.message_queue.get_nowait()
                self.insert_text_with_limit(self.output_window_text_box, message, self.MAX_RECOGNIZED_LINES)
        except Exception as e:
            logging.error(f"Error updating textbox: {e}")
        finally:
            self.root.after(100, self.update_textbox)

    # Periodically update the translation output box with messages from the translation queue
    def update_translation_box(self):
        try:
            while not self.translation_queue.empty():
                message = self.translation_queue.get_nowait()
                self.insert_text_with_limit(self.translated_text_box, message, self.MAX_TRANSLATED_LINES)
                new_text = message.strip()
                if new_text:
                    self.highlight_current_output_sentence(new_text)
                    if self.tts_input_source == "audio":
                        self.audio_tts_buffer += new_text + " "
                        if self.audio_tts_timer is not None:
                            self.root.after_cancel(self.audio_tts_timer)
                        self.audio_tts_timer = self.root.after(300, self.process_audio_tts_buffer)
                    else:
                        if new_text != self.last_spoken_text:
                            self.speak_text(new_text, origin=self.tts_input_source)
                            self.last_spoken_text = new_text
        except Exception as e:
            self.add_message_to_queue(f"Error updating translation box: {e}\n")
            logging.error(f"Error updating translation box: {e}")
        finally:
            self.root.after(100, self.update_translation_box)

    # Process buffered TTS audio text
    def process_audio_tts_buffer(self):
        if self.audio_tts_buffer.strip():
            self.speak_text(self.audio_tts_buffer.strip(), origin="audio")
            self.audio_tts_buffer = ""
        self.audio_tts_timer = None

    # Periodically process microphone level updates for the progress bar
    def process_mic_level_queue(self):
        try:
            while not self.mic_level_queue.empty():
                mic_level = self.mic_level_queue.get_nowait()
                self.mic_level.set(mic_level)
        except queue.Empty:
            pass
        except Exception as e:
            self.add_message_to_queue(f"Error processing microphone level: {e}\n")
            logging.error(f"Error processing microphone level: {e}")
        finally:
            self.root.after(100, self.process_mic_level_queue)

    # Remove overlapping text from consecutive recognition results
    def remove_overlap(self, new_text, previous_tail):
        translator_obj = str.maketrans('', '', string.punctuation)
        norm_new = new_text.lower().translate(translator_obj)
        norm_tail = previous_tail.lower().translate(translator_obj)
        new_words = norm_new.split()
        tail_words = norm_tail.split()
        if not tail_words or not new_words:
            return new_text
        matcher = difflib.SequenceMatcher(None, tail_words, new_words)
        match = matcher.find_longest_match(0, len(tail_words), 0, len(new_words))
        if match.size >= 2:
            original_new_words = new_text.split()
            cleaned = " ".join(original_new_words[match.b + match.size:])
            return cleaned
        return new_text

    # Process an audio buffer: recognize speech, remove overlaps, translate, and queue output
    def process_audio_buffer(self, spoken_language_code, target_language_code, audio_data):
        recognizer = sr.Recognizer()
        try:
            self.tts_input_source = "audio"
            logging.debug("Processing audio buffer...")
            combined_audio = np.concatenate(audio_data, axis=0)
            audio_data_int16 = np.int16(combined_audio * 32767)
            audio_bytes = audio_data_int16.tobytes()
            audio = sr.AudioData(audio_bytes, self.samplerate, 2)
            recognized_text = recognizer.recognize_google(audio, language=spoken_language_code)
            current_language = self.spoken_language_var.get()
            if recognized_text.strip():
                if self.last_reported_language != current_language:
                    self.add_message_to_queue(f"{current_language} selected ")
                    self.last_reported_language = current_language
                cleaned_text = self.remove_overlap(recognized_text, self.last_recognized_tail)
                self.last_recognized_tail = " ".join(recognized_text.split()[-5:])
                self.add_message_to_queue(f": {cleaned_text} ")
                logging.debug(f"Recognized Text: {cleaned_text}")
            else:
                logging.debug("No meaningful text recognized.")
            if self.map_language_for_translation(target_language_code) != self.map_language_for_translation(
                    spoken_language_code):
                translated_text = self.translate_text(recognized_text, target_language_code)
                if translated_text:
                    self.add_translation_to_queue(f"{translated_text} ")
                    logging.debug(f"Translated Text: {translated_text}")
            else:
                self.add_translation_to_queue(f"{recognized_text} ")
                logging.debug("Spoken and target languages are the same. No translation needed.")
        except sr.UnknownValueError:
            logging.error("Speech recognition could not understand audio.")
        except sr.RequestError as e:
            self.add_message_to_queue(f"Speech recognition error: {e}\n")
            logging.error(f"Speech recognition request error: {e}")
        except Exception as e:
            self.add_message_to_queue(f"Error processing audio: {e}\n")
            logging.exception("Unexpected error during audio processing.")

    # Wrapper for processing audio buffers in a separate thread
    def worker_thread(self, task):
        spoken_language_code, target_language_code, audio_data = task
        self.process_audio_buffer(spoken_language_code, target_language_code, audio_data)

    # Callback function for the audio input stream
    def audio_callback(self, indata, frames, time, status):
        try:
            if status:
                self.add_message_to_queue(f"Audio input error: {status}\n")
                logging.warning(f"Audio input error: {status}")
            indata = indata * self.gain
            silence_threshold = 0.02
            if np.linalg.norm(indata) < silence_threshold:
                logging.debug("Silence detected. Skipping this chunk.")
                return
            self.buffered_chunks.append(indata.copy())
            volume_norm = np.linalg.norm(indata) * 10
            mic_level = min(volume_norm, 100)
            self.mic_level_queue.put(mic_level)
            current_buffer_size = self.buffer_size_var.get()
            if len(self.buffered_chunks) >= current_buffer_size:
                spoken_language_code = self.current_spoken_language
                target_language_code = self.current_target_language
                self.executor.submit(self.worker_thread,
                                     (spoken_language_code, target_language_code, self.buffered_chunks.copy()))
                logging.debug(f"Enqueued audio buffer with {len(self.buffered_chunks)} chunks for processing.")
                overlap = self.overlap_percentage.get() / 100.0
                retain_chunks = int(overlap * len(self.buffered_chunks))
                self.buffered_chunks = self.buffered_chunks[-retain_chunks:] if retain_chunks > 0 else []
        except Exception as e:
            self.add_message_to_queue(f"Error in audio callback: {e}\n")
            logging.error(f"Error in audio callback: {e}")

    # Start capturing audio from the selected device
    def start_audio_capture(self, device_index):
        try:
            self.add_message_to_queue("Starting audio capture...\n")
            logging.info("Starting audio capture.")
            device_info = sd.query_devices(device_index, 'input')
            self.samplerate = int(device_info["default_samplerate"])
            with sd.InputStream(callback=self.audio_callback, channels=1, samplerate=self.samplerate,
                                device=device_index, blocksize=self.chunk_size):
                while self.is_listening and not self.audio_stop_event.is_set():
                    sd.sleep(50)
        except Exception as e:
            self.add_message_to_queue(f"Error during audio capture: {e}\n")
            logging.error(f"Error during audio capture: {e}")

    # Toggle the audio recognition state (start/stop)
    def toggle_recognition(self):
        try:
            self.is_listening = not self.is_listening
            if self.is_listening:
                self.start_button.config(text="Stop Audio Capture", bg="silver", fg="black")
                device_index = self.get_selected_device_index()
                if device_index is not None:
                    self.audio_stop_event.clear()
                    self.audio_thread = threading.Thread(target=self.start_audio_capture, args=(device_index,),
                                                         daemon=True)
                    self.audio_thread.start()
                    logging.info("Audio capture started.")
                    self.disable_buffer_size_control()
            else:
                self.start_button.config(text="Start Audio Capture", bg="silver", fg="black")
                self.add_message_to_queue("Stopped listening.\n")
                logging.info("Audio capture stopped.")
                self.audio_stop_event.set()
                self.enable_buffer_size_control()
        except Exception as e:
            self.add_message_to_queue(f"Error toggling recognition: {e}\n")
            logging.error(f"Error toggling recognition: {e}")

    # Get the index of the selected audio device from the combobox
    def get_selected_device_index(self):
        selected_device = self.device_combobox.get()
        if selected_device:
            try:
                device_index = int(selected_device.split(":")[0])
                logging.debug(f"Selected device index: {device_index}")
                return device_index
            except ValueError:
                self.add_message_to_queue("Invalid device selected.\n")
                logging.error("Invalid device selected.")
                return None
        self.add_message_to_queue("Please select an audio device.\n")
        logging.warning("No audio device selected.")
        return None

    # Save the transcript (recognized text and translated text) to a file
    def save_transcript(self):
        try:
            logging.debug("save_transcript method called.")
            if not self.root.winfo_viewable():
                self.root.deiconify()
                self.root.lift()
                self.root.focus_force()
                logging.debug("Main window restored and brought to focus.")
            self.root.attributes('-topmost', True)
            self.root.attributes('-topmost', False)
            self.root.update_idletasks()
            recognized_text = self.output_window_text_box.get("1.0", tk.END).strip()
            logging.debug(f"Recognized Text: {recognized_text}")
            translated_text = self.translated_text_box.get("1.0", tk.END).strip()
            logging.debug(f"Translated Text: {translated_text}")
            if recognized_text or translated_text:
                file_path = filedialog.asksaveasfilename(parent=self.root, defaultextension=".txt",
                                                         filetypes=[("Text files", "*.txt")],
                                                         title="Save Transcript As")
                logging.debug(f"Save dialog returned file path: {file_path}")
                if file_path:
                    try:
                        with open(file_path, "w", encoding="utf-8") as file:
                            file.write("Recognized Text:\n")
                            file.write(recognized_text + "\n\n")
                            file.write("Translated Text:\n")
                            file.write(translated_text)
                        self.add_message_to_queue(f"Transcript saved at: {file_path}\n")
                        logging.info(f"Transcript saved at: {file_path}")
                    except Exception as e:
                        self.add_message_to_queue(f"Error saving transcript: {e}\n")
                        logging.error(f"Error saving transcript: {e}")
            else:
                self.add_message_to_queue("No text to save!\n")
                logging.warning("Attempted to save transcript, but no text was available.")
        except Exception as e:
            self.add_message_to_queue(f"Error during transcript saving: {e}\n")
            logging.error(f"Error during transcript saving: {e}", exc_info=True)

    # Set the microphone gain based on slider value
    def set_gain(self, value):
        try:
            self.gain = float(value)
            db_gain = int(20 * np.log10(self.gain))
            self.add_message_to_queue(f"Microphone gain set to {self.gain}x ({db_gain} dB)\n")
            logging.info(f"Microphone gain set to {self.gain}x ({db_gain} dB)")
        except ValueError:
            self.add_message_to_queue("Invalid gain value.\n")
            logging.error("Invalid gain value entered.")

    # Map a language code for translation (handles some special cases)
    def map_language_for_translation(self, lang_code):
        if lang_code in ["he", "iw"]:
            return "iw"
        mapping = {
            'af': 'af', 'sq': 'sq', 'am': 'am', 'ar': 'ar', 'hy': 'hy', 'az': 'az',
            'eu': 'eu', 'be': 'be', 'bn': 'bn', 'bs': 'bs', 'bg': 'bg', 'ca': 'ca',
            'ceb': 'ceb', 'ny': 'ny', 'zh-CN': 'zh-CN', 'zh-TW': 'zh-TW',
            'co': 'co', 'hr': 'hr', 'cs': 'cs', 'da': 'da', 'nl': 'nl', 'en': 'en',
            'en-US': 'en', 'en-GB': 'en', 'eo': 'eo', 'et': 'et', 'tl': 'tl', 'fi': 'fi',
            'fr': 'fr', 'fy': 'fy', 'gl': 'gl', 'ka': 'ka', 'de': 'de', 'el': 'el',
            'gu': 'gu', 'ht': 'ht', 'ha': 'ha', 'hi': 'hi', 'hmn': 'hmn',
            'hu': 'hu', 'is': 'is', 'ig': 'ig', 'id': 'id', 'ga': 'ga', 'it': 'it',
            'ja': 'ja', 'jw': 'jw', 'kn': 'kn', 'kk': 'kk', 'km': 'km', 'rw': 'rw',
            'ko': 'ko', 'ku': 'ku', 'ky': 'ky', 'lo': 'lo', 'la': 'la', 'lv': 'lv',
            'lt': 'lt', 'lb': 'lb', 'mk': 'mk', 'mg': 'mg', 'ms': 'ms', 'ml': 'ml',
            'mt': 'mt', 'mi': 'mi', 'mr': 'mr', 'mn': 'mn', 'my': 'my', 'ne': 'ne',
            'no': 'no', 'or': 'or', 'ps': 'ps', 'fa': 'fa', 'pl': 'pl', 'pt': 'pt',
            'pa': 'pa', 'ro': 'ro', 'ru': 'ru', 'sm': 'sm', 'sr': 'sr', 'sk': 'sk',
            'sl': 'sl', 'so': 'so', 'es': 'es', 'su': 'su', 'sw': 'sw', 'sv': 'sv',
            'ta': 'ta', 'tt': 'tt', 'te': 'te', 'th': 'th', 'tr': 'tr', 'tk': 'tk',
            'uk': 'uk', 'ur': 'ur', 'ug': 'ug', 'uz': 'uz', 'vi': 'vi', 'cy': 'cy',
            'xh': 'xh', 'yi': 'yi', 'yo': 'yo', 'zu': 'zu'
        }
        mapped_lang = mapping.get(lang_code, 'en')
        logging.debug(f"Mapping language code '{lang_code}' to '{mapped_lang}'")
        return mapped_lang

    # Toggle the TTS state (enable or disable)
    def toggle_tts(self):
        try:
            if self.tts_enabled.get():
                self.add_message_to_queue("Text-to-Speech Enabled.\n")
                logging.info("Text-to-Speech enabled by user.")
            else:
                self.add_message_to_queue("Text-to-Speech Disabled.\n")
                logging.info("Text-to-Speech disabled by user.")
        except Exception as e:
            self.add_message_to_queue(f"Error toggling TTS: {e}\n")
            logging.error(f"Error toggling TTS: {e}")

    # Asynchronous function to convert text to speech using edge_tts
    async def async_speak_text(self, text, retry_count=3, origin="audio"):
        for attempt in range(1, retry_count + 1):
            if origin == "audio" and self.current_tts_text != text:
                logging.debug("TTS text changed. Cancelling current TTS.")
                return
            try:
                if not self.tts_enabled.get():
                    logging.debug("TTS is disabled. Skipping speech synthesis.")
                    return
                selected_voice_entry = self.voice_var.get()
                selected_voice_name = (selected_voice_entry.split(" - ")[1]
                                       if " - " in selected_voice_entry else selected_voice_entry)
                logging.debug(
                    f"Selected voice entry: '{selected_voice_entry}' parsed to voice name: '{selected_voice_name}'")
                selected_voice = next((voice for voice in self.edge_tts_voices if
                                       self.strip_voice_prefix(voice['Name']) == selected_voice_name), None)
                if not selected_voice:
                    error_message = f"Selected voice '{selected_voice_name}' not found."
                    self.add_message_to_queue(error_message + "\n")
                    logging.error(error_message)
                    return
                voice = selected_voice['ShortName']
                logging.debug(f"Using voice: {voice}")
                slider_value = self.tts_rate_var.get()
                if slider_value == 100:
                    logging.debug("Using default speed (no rate parameter).")
                    communicator = edge_tts.Communicate(text, voice=voice)
                else:
                    if slider_value > 100:
                        rate_str = f"+{int(slider_value - 100)}%"
                    else:
                        rate_str = f"-{int(100 - slider_value)}%"
                    logging.debug(f"Using rate string: {rate_str}")
                    communicator = edge_tts.Communicate(text, voice=voice, rate=rate_str)
                mp3_buffer = io.BytesIO()
                async for chunk in communicator.stream():
                    if origin == "audio" and self.current_tts_text != text:
                        logging.debug("TTS text changed during streaming. Cancelling current TTS.")
                        return
                    if chunk["type"] == "audio":
                        mp3_buffer.write(chunk["data"])
                if mp3_buffer.tell() == 0:
                    error_message = "No audio data received from TTS service."
                    self.add_message_to_queue(error_message + "\n")
                    logging.error(error_message)
                    raise ValueError("No audio data received.")
                mp3_buffer.seek(0)
                try:
                    audio_segment = AudioSegment.from_file(mp3_buffer, format="mp3")
                    wav_buffer = io.BytesIO()
                    audio_segment.export(wav_buffer, format="wav")
                    wav_buffer.seek(0)
                    logging.debug("MP3 to WAV conversion successful.")
                except Exception as e:
                    error_message = f"Error converting MP3 to WAV: {e}"
                    self.add_message_to_queue(error_message + "\n")
                    logging.error(error_message)
                    raise
                try:
                    fs, data = read(wav_buffer)
                    logging.debug(f"WAV file read successfully with sample rate: {fs}")
                except Exception as e:
                    error_message = f"Error reading WAV data: {e}"
                    self.add_message_to_queue(error_message + "\n")
                    logging.error(error_message)
                    raise
                device_name = self.tts_output_device_var.get()
                if device_name == "Default":
                    device_index = None
                    logging.debug("Using default TTS output device.")
                else:
                    try:
                        device_index = int(device_name.split(":")[0])
                        logging.debug(f"Selected TTS output device index: {device_index}")
                    except ValueError:
                        device_index = None
                        self.add_message_to_queue("Invalid TTS output device selected. Using default device.\n")
                        logging.error("Invalid TTS output device selected.")
                try:
                    sd.play(data, fs, device=device_index)
                    sd.wait()
                    logging.debug("TTS playback completed successfully.")
                    return
                except Exception as e:
                    error_message = f"Error during audio playback: {e}"
                    self.add_message_to_queue(error_message + "\n")
                    logging.error(error_message)
                    raise
            except Exception as e:
                if attempt < retry_count:
                    wait_time = 2 ** attempt
                    error_message = f"Attempt {attempt} failed: {e}. Retrying in {wait_time} seconds..."
                    self.add_message_to_queue(error_message + "\n")
                    logging.warning(error_message)
                    await asyncio.sleep(wait_time)
                else:
                    final_error = f"All {retry_count} attempts failed. Error with TTS: {e}"
                    self.add_message_to_queue(final_error + "\n")
                    logging.error(final_error)

    # Put text into the TTS processing queue
    def speak_text(self, text, origin="audio"):
        text = text.replace("\n", " ")
        max_tts_length = 2000
        if len(text) > max_tts_length:
            chunks = split_text_for_tts(text, max_len=max_tts_length)
            for chunk in chunks:
                if origin == "audio":
                    self.audio_tts_queue.put(chunk)
                else:
                    self.text_tts_queue.put(chunk)
        else:
            if origin == "audio":
                self.audio_tts_queue.put(text)
            else:
                self.text_tts_queue.put(text)
        if origin == "audio" and not self.audio_tts_processing:
            self.process_audio_tts_queue()
        elif origin != "audio" and not self.text_tts_processing:
            self.process_text_tts_queue()

    # Process the audio TTS queue in a background thread
    def process_audio_tts_queue(self):
        self.audio_tts_processing = True

        def worker():
            while not self.audio_tts_queue.empty():
                audio_text = self.audio_tts_queue.get()
                self.current_tts_text = audio_text
                coro = self.async_speak_text(audio_text, origin="audio")
                future = asyncio.run_coroutine_threadsafe(coro, self.tts_loop)
                try:
                    future.result()
                except Exception as e:
                    self.add_message_to_queue(f"Audio TTS error: {e}\n")
                    logging.error(f"Audio TTS error: {e}")
            self.audio_tts_processing = False

        threading.Thread(target=worker, daemon=True).start()

    # Process the text TTS queue in a background thread
    def process_text_tts_queue(self):
        self.text_tts_processing = True

        def worker():
            while not self.text_tts_queue.empty():
                text_to_speak = self.text_tts_queue.get()
                coro = self.async_speak_text(text_to_speak, origin="text")
                future = asyncio.run_coroutine_threadsafe(coro, self.tts_loop)
                try:
                    future.result()
                except Exception as e:
                    self.add_message_to_queue(f"Text TTS error: {e}\n")
                    logging.error(f"Text TTS error: {e}")
            self.text_tts_processing = False

        threading.Thread(target=worker, daemon=True).start()

    # Get a list of output audio devices for TTS playback
    def get_output_devices(self):
        try:
            devices = sd.query_devices()
            output_devices = ["Default"]
            for i, device in enumerate(devices):
                if device['max_output_channels'] > 0:
                    output_devices.append(f"{i}: {device['name']}")
            logging.debug(f"Available output devices: {output_devices}")
            return output_devices
        except Exception as e:
            self.add_message_to_queue(f"Error listing output devices: {e}\n")
            logging.error(f"Error listing output devices: {e}")
            return ["Default"]

    # Asynchronously fetch available TTS voices using edge_tts
    def list_edge_tts_voices(self):
        async def fetch_voices():
            try:
                voices = await edge_tts.list_voices()
                self.edge_tts_voices = voices
                voice_names = []
                for voice in voices:
                    stripped_name = self.strip_voice_prefix(voice['Name'])
                    country_name = self.get_country_name_from_locale(voice['Locale'])
                    display_name = f"{country_name} - {stripped_name}" if country_name else stripped_name
                    voice_names.append(display_name)
                    logging.debug(f"Processed voice: '{display_name}'")
                self.root.after(0, self.update_voice_combobox, voice_names)
                if voice_names:
                    self.add_message_to_queue("All TTS voices loaded into the combobox.\n")
                    logging.info("TTS voices loaded successfully.")
                else:
                    self.voice_combobox.set("No voices available")
                    self.voice_combobox.config(state="disabled")
                    self.add_message_to_queue("No TTS voices available.\n")
                    logging.warning("No TTS voices available.")
            except edge_tts.exceptions.NoVoiceError:
                error_message = "No voices found in the TTS service."
                self.add_message_to_queue(error_message + "\n")
                self.voice_combobox.set("No voices available")
                self.voice_combobox.config(state="disabled")
                logging.error(error_message)
            except Exception as e:
                error_message = f"Error fetching TTS voices: {e}"
                self.add_message_to_queue(error_message + "\n")
                self.voice_combobox.set("Error loading voices")
                self.voice_combobox.config(state="disabled")
                logging.error(error_message)

        if hasattr(self, 'tts_loop'):
            try:
                asyncio.run_coroutine_threadsafe(fetch_voices(), self.tts_loop)
                logging.debug("Scheduled fetching of TTS voices.")
            except Exception as e:
                self.add_message_to_queue(f"Error scheduling TTS voice fetching: {e}\n")
                logging.error(f"Error scheduling TTS voice fetching: {e}")
        else:
            self.add_message_to_queue("TTS event loop not initialized.\n")
            logging.error("TTS event loop not initialized.")

    # Update the voice combobox with fetched TTS voices
    def update_voice_combobox(self, voice_names):
        try:
            self.voice_combobox['values'] = voice_names
            target_index = 0
            for idx, name in enumerate(voice_names):
                if "sonianeural" in name.lower():
                    target_index = idx
                    break
            self.voice_combobox.current(target_index)
            logging.info(f"Default TTS voice set to index: {target_index} ({voice_names[target_index]})")
            self.voice_combobox.config(state="readonly")
            self.add_message_to_queue("Select a voice from the combobox.\n")
            logging.info("Voice selection updated.")
        except Exception as e:
            self.add_message_to_queue(f"Error updating voice combobox: {e}\n")
            logging.error(f"Error updating voice combobox: {e}")

    # Update the TTS voice selection based on target language changes
    def update_tts_voice_selection(self):
        if not hasattr(self, 'edge_tts_voices') or not self.edge_tts_voices:
            self.add_message_to_queue("TTS voices not loaded, cannot update TTS voice for target language.\n")
            return
        target_code = self.current_target_language.split('-')[0].lower()
        if target_code == "iw":
            target_code = "he"
        filtered = [voice for voice in self.edge_tts_voices if
                    voice.get("Locale", "").split('-')[0].lower() == target_code]
        if filtered:
            first_voice = filtered[0]
            stripped_name = self.strip_voice_prefix(first_voice['Name'])
            country_name = self.get_country_name_from_locale(first_voice['Locale'])
            display_name = f"{country_name} - {stripped_name}" if country_name else stripped_name
            self.voice_combobox.set(display_name)
            logging.info(f"TTS voice updated to: {display_name} for target language {self.target_language_var.get()}")
        else:
            self.add_message_to_queue("No TTS voice available for target language.\n")
            logging.error("No TTS voice available for target language.")

    # Update spoken language based on user selection
    def update_spoken_language(self, *args):
        try:
            self.current_spoken_language = self.languages.get(self.spoken_language_var.get(), "en")
            logging.debug(f"Spoken language updated to: {self.current_spoken_language}")
        except Exception as e:
            self.add_message_to_queue(f"Error updating spoken language: {e}\n")
            logging.error(f"Error updating spoken language: {e}")

    # Update target language based on user selection and update TTS voice accordingly
    def update_target_language(self, *args):
        try:
            self.current_target_language = self.languages.get(self.target_language_var.get(), "en")
            logging.debug(f"Target language updated to: {self.current_target_language}")
            self.update_tts_voice_selection()
        except Exception as e:
            self.add_message_to_queue(f"Error updating target language: {e}\n")
            logging.error(f"Error updating target language: {e}")

    # Disable the buffer size slider when audio capture is active
    def disable_buffer_size_control(self):
        try:
            self.buffer_size_slider.config(state='disabled')
            logging.debug("Buffer size control disabled during audio capture.")
        except Exception as e:
            self.add_message_to_queue(f"Error disabling buffer size control: {e}\n")
            logging.error(f"Error disabling buffer size control: {e}")

    # Enable the buffer size slider when audio capture stops
    def enable_buffer_size_control(self):
        try:
            self.buffer_size_slider.config(state='normal')
            logging.debug("Buffer size control enabled after stopping audio capture.")
        except Exception as e:
            self.add_message_to_queue(f"Error enabling buffer size control: {e}\n")
            logging.error(f"Error enabling buffer size control: {e}")

    # Remove a common prefix from TTS voice names for display purposes
    def strip_voice_prefix(self, voice_name):
        prefix = "Microsoft Server Speech Text to Speech Voice "
        if voice_name.lower().startswith(prefix.lower()):
            stripped_name = voice_name[len(prefix):].strip("'\" ")
            logging.debug(f"Stripped voice name: '{stripped_name}' from original '{voice_name}'")
            return stripped_name
        logging.debug(f"No prefix found to strip for voice name: '{voice_name}'")
        return voice_name

    # Batch translation: process a document in segments on a background thread with a progress window.
    def batch_translate_in_background(self):
        # Turn off TTS during batch translation.
        self.tts_enabled.set(False)
        self.add_message_to_queue("TTS turned off for batch translation.\n")

        # Gather text from listbox or textbox.
        text = ""
        if self.input_listbox is not None and self.input_listbox.size() > 0:
            items = self.input_listbox.get(0, tk.END)
            text = "\n".join(items)
        elif self.input_text_box is not None:
            text = self.input_text_box.get("1.0", tk.END).strip()
        else:
            self.root.after(0,
                            lambda: messagebox.showinfo("No Document", "No text document is loaded for translation."))
            return
        if not text.strip():
            self.root.after(0, lambda: messagebox.showinfo("Empty Document", "The loaded document is empty."))
            return

        # Create a modal progress window.
        def create_progress_window():
            progress_win = tk.Toplevel(self.root)
            progress_win.title("Translating Document")
            progress_win.geometry("350x100")
            progress_label = tk.Label(progress_win, text="Translating...")
            progress_label.pack(padx=10, pady=10)
            progress_bar = ttk.Progressbar(progress_win, orient="horizontal", mode="determinate", length=300)
            progress_bar.pack(padx=10, pady=10)
            return progress_win, progress_bar

        progress_win, progress_bar = create_progress_window()

        # Clear previous output and translation cache.
        self.root.after(0, lambda: self.translated_text_box.delete("1.0", tk.END))
        with self.cache_lock:
            self.translation_cache.clear()

        # Split the document into manageable segments.
        segments = split_text_with_fallback(text, fallback_word_count=300)
        merged_segments = merge_short_segments(segments, min_word_count=3, min_char_threshold=4)
        total_segments = len(merged_segments)

        # Set the progress bar maximum value.
        self.root.after(0, lambda: progress_bar.config(maximum=total_segments))

        translated_segments = []
        # Translate each segment sequentially.
        for idx, seg in enumerate(merged_segments):
            translated_seg = self._translate_single(seg, self.current_target_language)
            if translated_seg is None:
                translated_seg = ""
            translated_segments.append(translated_seg)
            # Update the progress bar on the main thread.
            self.root.after(0, lambda v=idx + 1: progress_bar.config(value=v))
            self.add_message_to_queue(f"Wait.Translating {idx + 1}/{total_segments}.\n")

        translated_text = " ".join(translated_segments)
        self.root.after(0, lambda: self.translated_text_box.insert(tk.END, translated_text))
        self.add_message_to_queue("Batch translation completed.\n")

        # Close the progress window.
        self.root.after(0, progress_win.destroy)

    # Entry point for batch translation from the translation window; runs in a background thread.
    def batch_translate_document(self):
        threading.Thread(target=self.batch_translate_in_background, daemon=True).start()


# Main program execution: create the main window and run the application loop.
if __name__ == "__main__":
    try:
        root = tk.Tk()
        app = TranslatorApp(root)
        root.mainloop()
    except Exception as e:
        logging.critical(f"Unhandled exception: {e}", exc_info=True)
    finally:
        if 'app' in locals():
            app.executor.shutdown(wait=True)
            logging.info("ThreadPoolExecutor shutdown in finally block.")
            app.stop_tts_loop()
