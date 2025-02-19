import os
import subprocess

# (Do not monkey-patch here!)

import tkinter as tk  # Standard Python library for GUI applications
from tkinter import ttk, filedialog, messagebox  # Themed widgets, file dialogs, and message boxes
import tkinter.font as tkfont  # For dynamic font scaling
import sounddevice as sd  # Access to audio input/output devices
import numpy as np  # Numerical operations on arrays
import speech_recognition as sr  # Speech-to-text functionality
from deep_translator import GoogleTranslator  # GoogleTranslator for translation
import threading  # For running tasks in the background
import queue  # Queue for communication between threads
from scipy.io.wavfile import write, read  # Save and read audio data to/from a file
from pystray import Icon, Menu, MenuItem  # For system tray functionality
from PIL import Image, ImageDraw  # For image handling for the system tray icon
import asyncio  # For asynchronous operations with edge-tts

# Now that asyncio and its windows modules are imported, we can safely apply our monkey-patch.
if os.name == "nt":
    CREATE_NO_WINDOW = 0x08000000  # Windows flag to hide console window
    original_popen = subprocess.Popen
    def no_window_popen(*args, **kwargs):
        if os.name == "nt":
            kwargs.setdefault("creationflags", CREATE_NO_WINDOW)
        return original_popen(*args, **kwargs)
    subprocess.Popen = no_window_popen

import edge_tts  # Text-to-Speech library using Microsoft Edge
from pydub import AudioSegment  # For audio format conversion
import tempfile  # For creating temporary files
import sys  # For system-specific parameters and functions
from collections import OrderedDict  # For implementing an LRU cache
import io  # For in-memory byte streams
import logging  # For detailed logging
from concurrent.futures import ThreadPoolExecutor  # For managing worker threads
import pycountry  # For mapping locale codes to full language names

# Configure logging
log_file = os.path.join(os.path.expanduser("~"), "translator_app_debug.log")
logging.basicConfig(
    level=logging.DEBUG,
    format='%(asctime)s - %(levelname)s - %(message)s',
    filename=log_file,
    filemode='a'  # Append mode to preserve logs across sessions
)


class TranslatorApp:
    def __init__(self, root):
        """
        Initialize the TranslatorApp class, set up the GUI components, configure threads and queues,
        and add dynamic resizing support.
        """
        self.root = root
        self.is_listening = False  # Flag to control audio capture state
        self.samplerate = 16000  # Initial sample rate (will be updated per device)
        self.chunk_size = 2048  # Size of each audio chunk to be processed
        self.buffered_chunks = []  # Buffer to hold audio chunks for processing
        self.gain = 1.0  # Microphone gain factor (1.0 = no gain)
        self.languages_swapped = False  # Tracks whether spoken/target languages are swapped
        self.message_queue = queue.Queue()  # Queue for recognized messages
        self.translation_queue = queue.Queue()  # Queue for translated messages
        self.task_queue = queue.Queue()  # Queue for audio processing tasks

        # Define maximum number of lines for text boxes to prevent sluggishness
        self.MAX_RECOGNIZED_LINES = 100
        self.MAX_TRANSLATED_LINES = 100

        # Initialize Text-to-Speech variables using edge-tts
        self.tts_enabled = tk.BooleanVar()
        self.tts_enabled.set(False)  # Default: TTS disabled
        self.voice_var = tk.StringVar()
        self.voice_var.set("Loading voices...")  # Initial placeholder

        # Font Size Variable for translated text (controlled by slider)
        self.font_size_var = tk.IntVar()
        self.font_size_var.set(20)  # Default font size for translated text

        # Output device selection for TTS
        self.tts_output_device_var = tk.StringVar()
        self.tts_output_device_var.set("Default")  # Default output device

        # Initialize a queue for microphone levels
        self.mic_level_queue = queue.Queue()

        # Initialize the Translation Cache
        self.translation_cache = OrderedDict()  # To store (text, target_language): translated_text
        self.cache_lock = threading.Lock()  # Ensure thread-safe access to the cache
        self.cache_size = 1000  # Maximum number of cached translations

        # Get screen width and height for scaling purposes
        screen_width = self.root.winfo_screenwidth()
        screen_height = self.root.winfo_screenheight()

        # Define a scaling factor based on screen size (reduced to 75% for a more compact GUI)
        self.scale_factor = min(screen_width / 800, screen_height / 700) * 0.75

        # Define a design baseline (in pixels) for dynamic resizing
        self.design_width = 600
        self.design_height = 600

        # Set initial Tk scaling
        self.root.tk.call('tk', 'scaling', self.scale_factor)

        # Create instance fonts that will be dynamically updated
        self.label_font = tkfont.Font(family="Arial", size=int(10.5 * self.scale_factor))
        self.dropdown_font = tkfont.Font(family="Arial", size=int(9 * self.scale_factor))
        self.button_font = tkfont.Font(family="Arial", size=int(10.5 * self.scale_factor))
        self.text_font = tkfont.Font(family="Arial", size=int(10.5 * self.scale_factor))

        # Set the minimum window size
        combobox_width = int(60 * self.scale_factor)
        self.root.minsize(combobox_width + 150, int(600 * self.scale_factor))

        # Initialize shared language variables
        self.languages = self.get_language_dict()
        self.language_code_to_name = {code: name for name, code in self.languages.items()}  # Reverse mapping
        self.current_spoken_language = self.languages.get("English (US)", "en")
        self.current_target_language = self.languages.get("English (US)", "en")

        # Initialize Buffer Size Variable
        self.buffer_size_var = tk.IntVar()
        self.buffer_size_var.set(40)  # Default buffer size set to 40 (Changed from 100)
        self.buffer_size = self.buffer_size_var.get()

        # Configure pydub to use the bundled ffmpeg
        self.configure_ffmpeg()

        # Create GUI components (text boxes, buttons, labels, etc.)
        self.create_widgets()

        # Automatically list audio devices at startup
        self.list_audio_devices()

        # Schedule recurring tasks to update the GUI and monitor microphone levels
        self.root.after(100, self.update_textbox)
        self.root.after(100, self.update_translation_box)
        self.root.after(100, self.process_mic_level_queue)

        # Start background threads for audio capture and processing
        self.audio_thread = None
        self.audio_stop_event = threading.Event()

        # Initialize TTS event loop in a separate thread
        self.tts_loop = asyncio.new_event_loop()
        self.tts_thread = threading.Thread(target=self.start_tts_loop, daemon=True)
        self.tts_thread.start()

        # Initialize ThreadPoolExecutor for audio processing
        self.executor = ThreadPoolExecutor(max_workers=2)

        # Start a thread to list all available TTS voices using edge-tts
        self.list_edge_tts_voices()

        # Setup trace callbacks for language selection changes
        self.spoken_language_var.trace_add('write', self.update_spoken_language)
        self.target_language_var.trace_add('write', self.update_target_language)

        # Bind the <Configure> event to enable dynamic resizing of fonts and scaling
        self.root.bind("<Configure>", self.on_resize)

    def on_resize(self, event):
        """Handle dynamic resizing."""
        if event.widget == self.root:
            new_scale = min(event.width / self.design_width, event.height / self.design_height)
            if abs(new_scale - self.scale_factor) > 0.01:
                self.scale_factor = new_scale
                self.root.tk.call('tk', 'scaling', self.scale_factor)
                self.label_font.configure(size=int(10.5 * self.scale_factor))
                self.dropdown_font.configure(size=int(9 * self.scale_factor))
                self.button_font.configure(size=int(10.5 * self.scale_factor))
                self.text_font.configure(size=int(10.5 * self.scale_factor))
                logging.debug(f"Dynamic resize: new scale factor set to {self.scale_factor}")

    def start_tts_loop(self):
        """Start the asyncio event loop for TTS."""
        asyncio.set_event_loop(self.tts_loop)
        try:
            self.tts_loop.run_forever()
        except Exception as e:
            self.add_message_to_queue(f"TTS event loop error: {e}\n")
            logging.error(f"TTS event loop error: {e}")

    def configure_ffmpeg(self):
        """Configure ffmpeg for pydub."""
        try:
            import shutil
            if getattr(sys, 'frozen', False):
                base_path = sys._MEIPASS
                ffmpeg_executable = 'ffmpeg.exe' if os.name == 'nt' else 'ffmpeg'
                ffmpeg_path = os.path.join(base_path, 'ffmpeg', 'bin', ffmpeg_executable)
                if os.path.isfile(ffmpeg_path):
                    AudioSegment.converter = ffmpeg_path
                    logging.debug(f"Configured ffmpeg path to bundled executable: {ffmpeg_path}")
                else:
                    logging.warning(f"Bundled ffmpeg not found at: {ffmpeg_path}. Using system ffmpeg.")
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

    def create_widgets(self):
        """Create and arrange GUI widgets using pack for top_frame controls."""
        self.root.title("Real-Time Language Translator")
        self.root.geometry(f"{int(600 * self.scale_factor)}x{int(600 * self.scale_factor)}")
        self.root.configure(bg="#f4f4f4")

        # Create a top_frame without horizontal padding so controls align to the left.
        top_frame = tk.Frame(self.root, bg="#e0e0e0", bd=2, relief="groove", padx=0, pady=int(7.5 * self.scale_factor))
        top_frame.pack(side=tk.TOP, fill="x")
        # Create a bottom_frame for the rest of the controls.
        bottom_frame = tk.Frame(self.root, bg="#e0e0e0", bd=2, relief="groove",
                                padx=int(7.5 * self.scale_factor),
                                pady=int(7.5 * self.scale_factor))
        bottom_frame.pack(side=tk.BOTTOM, fill="x")

        # Create a language frame (for language controls) and pack it flush left.
        lang_frame = tk.Frame(top_frame, bg="#e0e0e0")
        lang_frame.pack(side="top", anchor="w", fill="x", padx=0)

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

        self.swap_button = tk.Button(lang_frame, text="Swap Languages", command=self.swap_languages,
                                     bg="#FFC107", fg="black", font=self.button_font, relief="raised", bd=4)
        self.swap_button.pack(anchor="w", pady=(0, 5))

        # Create a device frame for the device controls.
        # We add a left padding equal to 60 pixels so that device controls appear 60 px to the right of language controls.
        device_frame = tk.Frame(top_frame, bg="#e0e0e0")
        device_frame.pack(side="top", anchor="w", fill="x", padx=(60, 0), pady=(int(7.5 * self.scale_factor), 0))
        device_label = tk.Label(device_frame, text="Select Microphone Device:", bg="#e0e0e0", fg="black",
                                font=self.label_font)
        device_label.pack(anchor="w")
        self.device_combobox = ttk.Combobox(device_frame, state="readonly", font=self.dropdown_font, width=60)
        self.device_combobox.pack(anchor="w", pady=(0, int(3.75 * self.scale_factor)))

        # Bottom frame widgets (using pack)
        self.mic_level = tk.DoubleVar()
        mic_progress = ttk.Progressbar(bottom_frame, orient="horizontal", mode="determinate",
                                       length=int(375 * self.scale_factor), variable=self.mic_level, maximum=100)
        mic_progress.pack(pady=int(7.5 * self.scale_factor))
        self.start_button = tk.Button(bottom_frame, text="Start Audio Capture", command=self.toggle_recognition,
                                      bg="#4CAF50", fg="white", font=self.button_font, relief="raised", bd=4)
        self.start_button.pack(pady=int(7.5 * self.scale_factor))
        gain_slider = tk.Scale(bottom_frame, from_=1.0, to_=4.0, resolution=0.1, orient="horizontal", label="Mic Gain",
                               length=int(225 * self.scale_factor), command=self.set_gain, font=self.label_font)
        gain_slider.set(1.0)
        gain_slider.pack(pady=int(7.5 * self.scale_factor))
        buffer_size_frame = tk.Frame(bottom_frame, bg="#e0e0e0")
        buffer_size_frame.pack(pady=int(7.5 * self.scale_factor))
        buffer_size_label = tk.Label(buffer_size_frame, text="Buffer Size:", bg="#e0e0e0", fg="black",
                                     font=self.label_font)
        buffer_size_label.pack(side="left", padx=(0, 10))
        self.buffer_size_slider = tk.Scale(buffer_size_frame, from_=20, to=120, resolution=10, orient="horizontal",
                                           variable=self.buffer_size_var, command=self.update_buffer_size,
                                           length=int(200 * self.scale_factor), font=self.dropdown_font)
        self.buffer_size_slider.pack(side="left")
        self.buffer_size_slider.set(40)
        self.output_window_text_box = tk.Text(self.root, height=int(15 * self.scale_factor),
                                              width=int(60 * self.scale_factor), bg="#ffffff",
                                              font=self.text_font, bd=3, relief="sunken")
        self.output_window_text_box.pack(side="left", padx=int(7.5 * self.scale_factor),
                                         pady=int(7.5 * self.scale_factor))
        save_button = tk.Button(bottom_frame, text="Save Transcript", command=self.save_transcript, bg="#4CAF50",
                                fg="white", font=self.button_font, relief="raised", bd=4)
        save_button.pack(pady=int(7.5 * self.scale_factor))
        exit_button = tk.Button(bottom_frame, text="Halt and Clean Exit", command=self.halt_and_exit,
                                bg="red", fg="white", font=self.button_font, relief="raised", bd=4)
        exit_button.pack(pady=int(7.5 * self.scale_factor))
        minimize_button = tk.Button(bottom_frame, text="Minimize to Tray", command=self.minimize_to_tray,
                                    bg="#FFC107", fg="black", font=self.button_font, relief="raised", bd=4)
        minimize_button.pack(pady=int(7.5 * self.scale_factor))
        self.create_translation_window()

    def get_full_language_name(self, locale_code):
        """Convert a locale code to a full language name using pycountry."""
        try:
            language_part, country_part = locale_code.split('-')
            language = pycountry.languages.get(alpha_2=language_part)
            country = pycountry.countries.get(alpha_2=country_part)
            if language and country:
                return f"{language.name} ({country.name})"
            elif language:
                return language.name
            else:
                return locale_code
        except Exception:
            return locale_code

    def update_buffer_size(self, value):
        """Update the buffer size based on the slider's value."""
        try:
            buffer_size = int(value)
            if 20 <= buffer_size <= 120:
                self.buffer_size = buffer_size
                self.add_message_to_queue(f"Buffer size set to: {buffer_size}\n")
                logging.info(f"Buffer size updated to: {buffer_size}")
            else:
                self.add_message_to_queue("Buffer size must be between 20 and 120.\n")
                logging.warning("Attempted to set buffer size outside allowed range.")
        except ValueError:
            self.add_message_to_queue("Invalid buffer size value.\n")
            logging.error("Invalid buffer size value entered.")

    def create_translation_window(self):
        """Create a separate window for translation display and TTS controls."""
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
                                           font=("Arial", self.font_size_var.get()), bd=3,
                                           relief="sunken")
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
        voice_label = tk.Label(voice_frame, text="Select Voice:", bg="#f4f4f4", fg="black",
                               font=self.label_font)
        voice_label.pack(side="left", padx=(0, 10))
        self.voice_combobox = ttk.Combobox(voice_frame, textvariable=self.voice_var,
                                           values=["Loading voices..."], state="disabled",
                                           font=self.dropdown_font, width=50)
        self.voice_combobox.pack(side="left")
        font_size_frame = tk.Frame(translation_window, bg="#f4f4f4")
        font_size_frame.grid(row=3, column=0, sticky="ew", padx=int(10 * self.scale_factor), pady=(5, 10))
        font_size_label = tk.Label(font_size_frame, text="Translated Text Font Size:", bg="#f4f4f4", fg="black",
                                   font=self.label_font)
        font_size_label.pack(side="left", padx=(0, 10))
        font_size_slider = tk.Scale(font_size_frame, from_=10, to=40, orient="horizontal", label="",
                                    length=int(200 * self.scale_factor), variable=self.font_size_var,
                                    command=self.set_translation_font_size, font=self.dropdown_font)
        font_size_slider.set(20)
        font_size_slider.pack(side="left", padx=(10, 0), pady=5)

    def set_translation_font_size(self, size):
        """Adjust the font size of the translated text box."""
        try:
            new_font = ("Arial", int(size))
            self.translated_text_box.config(font=new_font)
            logging.info(f"Translated text font size set to: {size}")
        except ValueError:
            self.add_message_to_queue("Invalid font size selected.\n")
            logging.error("Invalid font size selected.")

    def swap_languages(self):
        """Swap the spoken and target languages."""
        try:
            if self.spoken_language_var.get() == self.target_language_var.get():
                messagebox.showinfo("Swap Languages", "Spoken and target languages are the same. Swap not required.")
                logging.info("Attempted to swap languages, but both languages are the same.")
                return
            original_spoken = self.spoken_language_var.get()
            self.spoken_language_var.set(self.target_language_var.get())
            self.target_language_var.set(original_spoken)
            if not self.languages_swapped:
                self.swap_button.config(text="Swap Back", bg="#4CAF50")
                self.languages_swapped = True
                logging.info("Languages swapped: Spoken and target languages exchanged.")
            else:
                self.swap_button.config(text="Swap Languages", bg="#FFC107")
                self.languages_swapped = False
                logging.info("Languages swapped back to original configuration.")
        except Exception as e:
            self.add_message_to_queue(f"Error swapping languages: {e}\n")
            logging.error(f"Error swapping languages: {e}")

    def list_audio_devices(self):
        """List available microphone devices and mark WASAPI devices."""
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
                    device_list.append(f"{i}: {wasapi_prefix}{device['name']} (Input Channels: {device['max_input_channels']})")
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

    def halt_and_exit(self):
        """Cleanly exit the application."""
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

    def minimize_to_tray(self):
        """Minimize the application to the system tray."""
        try:
            icon_image = Image.new('RGB', (64, 64), (255, 255, 255))
            draw = ImageDraw.Draw(icon_image)
            draw.rectangle((0, 0, 64, 64), fill=(0, 100, 255))
            icon_image = icon_image.resize((64, 64))
            menu = Menu(
                MenuItem('Restore', self.restore_from_tray),
                MenuItem('Exit', self.halt_and_exit)
            )
            self.tray_icon = Icon("TranslatorApp", icon_image, "Translator", menu)
            self.root.withdraw()
            logging.info("Application minimized to system tray.")
            threading.Thread(target=self.tray_icon.run, daemon=True).start()
        except Exception as e:
            self.add_message_to_queue(f"Error minimizing to tray: {e}\n")
            logging.error(f"Error minimizing to tray: {e}")

    def restore_from_tray(self, icon, item):
        """Restore the application from the system tray."""
        try:
            self.tray_icon.stop()
            self.root.deiconify()
            logging.info("Application restored from system tray.")
        except Exception as e:
            self.add_message_to_queue(f"Error restoring from tray: {e}\n")
            logging.error(f"Error restoring from tray: {e}")

    def get_language_dict(self):
        """Return a dictionary mapping language names to ISO codes."""
        return {
            "Afrikaans": "af", "Albanian": "sq", "Amharic": "am", "Arabic": "ar", "Armenian": "hy", "Azerbaijani": "az",
            "Basque": "eu", "Belarusian": "be", "Bengali": "bn", "Bosnian": "bs", "Bulgarian": "bg", "Catalan": "ca",
            "Cebuano": "ceb", "Chichewa": "ny", "Chinese (Simplified)": "zh-CN", "Chinese (Traditional)": "zh-TW",
            "Corsican": "co", "Croatian": "hr", "Czech": "cs", "Danish": "da", "Dutch": "nl", "English (US)": "en-US",
            "English (UK)": "en-GB", "Esperanto": "eo", "Estonian": "et", "Filipino": "tl", "Finnish": "fi",
            "French": "fr", "Frisian": "fy", "Galician": "gl", "Georgian": "ka", "German": "de", "Greek": "el",
            "Gujarati": "gu", "Haitian Creole": "ht", "Hausa": "ha", "Hebrew": "he", "Hindi": "hi", "Hmong": "hmn",
            "Hungarian": "hu", "Icelandic": "is", "Igbo": "ig", "Indonesian": "id", "Irish": "ga", "Italian": "it",
            "Japanese": "ja", "Javanese": "jw", "Kannada": "kn", "Kazakh": "kk", "Khmer": "km", "Kinyarwanda": "rw",
            "Korean": "ko", "Kurdish (Kurmanji)": "ku", "Kyrgyz": "ky", "Lao": "lo", "Latin": "la", "Latvian": "lv",
            "Lithuanian": "lt", "Luxembourgish": "lb", "Macedonian": "mk", "Malagasy": "mg", "Malay": "ms",
            "Malayalam": "ml", "Maltese": "mt", "Maori": "mi", "Marathi": "mr", "Mongolian": "mn",
            "Myanmar": "my", "Nepali": "ne", "Norwegian": "no", "Odia": "or", "Pashto": "ps", "Persian": "fa",
            "Polish": "pl", "Portuguese": "pt", "Punjabi": "pa", "Romanian": "ro", "Russian": "ru", "Samoan": "sm",
            "Scots Gaelic": "gd", "Serbian": "sr", "Sesotho": "st", "Shona": "sn", "Sindhi": "sd", "Sinhala": "si",
            "Slovak": "sk", "Slovenian": "sl", "Somali": "so", "Spanish": "es", "Sundanese": "su", "Swahili": "sw",
            "Swedish": "sv", "Tajik": "tg", "Tamil": "ta", "Tatar": "tt", "Telugu": "te", "Thai": "th",
            "Turkish": "tr", "Turkmen": "tk", "Ukrainian": "uk", "Urdu": "ur", "Uyghur": "ug", "Uzbek": "uz",
            "Vietnamese": "vi", "Welsh": "cy", "Xhosa": "xh", "Yiddish": "yi", "Yoruba": "yo", "Zulu": "zu"
        }

    def add_message_to_queue(self, message):
        """Add a message to the message queue and log it."""
        self.message_queue.put(message)
        logging.debug(message.strip())

    def add_translation_to_queue(self, message):
        """Add a translated message to the translation queue and log it."""
        self.translation_queue.put(message)
        logging.debug(f"Translation added to queue: {message.strip()}")

    def insert_text_with_limit(self, text_widget, message, max_lines):
        """Insert text into a widget while limiting the number of lines."""
        text_widget.insert(tk.END, message)
        text_widget.see(tk.END)
        current_lines = int(text_widget.index('end-1c').split('.')[0])
        if current_lines > max_lines:
            lines_to_delete = current_lines - max_lines
            text_widget.delete(f"1.0", f"{lines_to_delete + 1}.0")
            logging.debug(f"Deleted {lines_to_delete} lines from the text box to maintain max lines.")

    def update_textbox(self):
        """Check for new messages and update the output text box."""
        try:
            while not self.message_queue.empty():
                message = self.message_queue.get_nowait()
                self.insert_text_with_limit(self.output_window_text_box, message, self.MAX_RECOGNIZED_LINES)
        except Exception as e:
            logging.error(f"Error updating textbox: {e}")
        finally:
            self.root.after(100, self.update_textbox)

    def update_translation_box(self):
        """Check for new translations and update the translation text box."""
        try:
            while not self.translation_queue.empty():
                message = self.translation_queue.get_nowait()
                self.insert_text_with_limit(self.translated_text_box, message, self.MAX_TRANSLATED_LINES)
                self.speak_text(message.strip())
        except Exception as e:
            self.add_message_to_queue(f"Error updating translation box: {e}\n")
            logging.error(f"Error updating translation box: {e}")
        finally:
            self.root.after(100, self.update_translation_box)

    def process_mic_level_queue(self):
        """Process the microphone level queue and update the corresponding variable."""
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

    def process_audio_buffer(self, spoken_language_code, target_language_code, audio_data):
        """Process buffered audio for speech recognition and translation."""
        recognizer = sr.Recognizer()
        try:
            logging.debug("Processing audio buffer...")
            combined_audio = np.concatenate(audio_data, axis=0)
            audio_data_int16 = np.int16(combined_audio * 32767)
            audio_bytes = audio_data_int16.tobytes()
            audio = sr.AudioData(audio_bytes, self.samplerate, 2)
            recognized_text = recognizer.recognize_google(audio, language=spoken_language_code)
            if recognized_text.strip():
                self.add_message_to_queue(f"Recognized ({self.spoken_language_var.get()}): {recognized_text}\n")
                logging.debug(f"Recognized Text: {recognized_text}")
            else:
                logging.debug("No meaningful text recognized.")
            if target_language_code != self.map_language_for_translation(spoken_language_code):
                translated_text = self.translate_text(recognized_text, target_language_code)
                if translated_text:
                    self.add_translation_to_queue(f"{translated_text}\n")
                    logging.debug(f"Translated Text: {translated_text}")
            else:
                self.add_translation_to_queue(f"{recognized_text}\n")
                logging.debug("Spoken and target languages are the same. No translation needed.")
        except sr.UnknownValueError:
            logging.error("Speech recognition could not understand audio.")
        except sr.RequestError as e:
            self.add_message_to_queue(f"Speech recognition error: {e}\n")
            logging.error(f"Speech recognition request error: {e}")
        except Exception as e:
            self.add_message_to_queue(f"Error processing audio: {e}\n")
            logging.exception("Unexpected error during audio processing.")

    def translate_text(self, text, target_language):
        """Translate text using GoogleTranslator with caching."""
        cache_key = (text.lower(), target_language)
        with self.cache_lock:
            if cache_key in self.translation_cache:
                self.translation_cache.move_to_end(cache_key)
                cached_translation = self.translation_cache[cache_key]
                logging.debug("Translation retrieved from cache.")
                return cached_translation
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
                    logging.debug("Oldest translation removed from cache to maintain size.")
            return translated
        except Exception as e:
            self.add_translation_to_queue(f"Translation failed: {e}\n")
            logging.error(f"Translation failed: {e}")
            return None

    def worker_thread(self, task):
        """Background worker for processing audio data."""
        spoken_language_code, target_language_code, audio_data = task
        self.process_audio_buffer(spoken_language_code, target_language_code, audio_data)

    def audio_callback(self, indata, frames, time, status):
        """Callback for real-time audio capture."""
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
                retain_chunks = int(0.2 * len(self.buffered_chunks))
                self.buffered_chunks = self.buffered_chunks[-retain_chunks:]
        except Exception as e:
            self.add_message_to_queue(f"Error in audio callback: {e}\n")
            logging.error(f"Error in audio callback: {e}")

    def start_audio_capture(self, device_index):
        """
        Start continuous audio capture using the selected device.
        For WASAPI devices, we query the device’s default sample rate.
        """
        try:
            self.add_message_to_queue("Starting audio capture...\n")
            logging.info("Starting audio capture.")
            device_info = sd.query_devices(device_index, 'input')
            # Update self.samplerate to the device's default sample rate
            self.samplerate = int(device_info["default_samplerate"])
            with sd.InputStream(callback=self.audio_callback, channels=1, samplerate=self.samplerate,
                                device=device_index, blocksize=self.chunk_size):
                while self.is_listening and not self.audio_stop_event.is_set():
                    sd.sleep(50)
        except Exception as e:
            self.add_message_to_queue(f"Error during audio capture: {e}\n")
            logging.error(f"Error during audio capture: {e}")

    def toggle_recognition(self):
        """Toggle starting/stopping audio capture."""
        try:
            self.is_listening = not self.is_listening
            if self.is_listening:
                self.start_button.config(text="Stop Audio Capture", bg="red")
                device_index = self.get_selected_device_index()
                if device_index is not None:
                    self.audio_stop_event.clear()
                    self.audio_thread = threading.Thread(target=self.start_audio_capture, args=(device_index,),
                                                         daemon=True)
                    self.audio_thread.start()
                    logging.info("Audio capture started.")
                    self.disable_buffer_size_control()
            else:
                self.start_button.config(text="Start Audio Capture", bg="#4CAF50")
                self.add_message_to_queue("Stopped listening.\n")
                logging.info("Audio capture stopped.")
                self.audio_stop_event.set()
                self.enable_buffer_size_control()
        except Exception as e:
            self.add_message_to_queue(f"Error toggling recognition: {e}\n")
            logging.error(f"Error toggling recognition: {e}")

    def get_selected_device_index(self):
        """Retrieve the selected device index from the device combobox."""
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

    def save_transcript(self):
        """Save recognized and translated text to a file."""
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
                file_path = filedialog.asksaveasfilename(
                    parent=self.root,
                    defaultextension=".txt",
                    filetypes=[("Text files", "*.txt")],
                    title="Save Transcript As"
                )
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

    def set_gain(self, value):
        """Adjust the microphone gain based on the slider value."""
        try:
            self.gain = float(value)
            db_gain = int(20 * np.log10(self.gain))
            self.add_message_to_queue(f"Microphone gain set to {self.gain}x ({db_gain} dB)\n")
            logging.info(f"Microphone gain set to {self.gain}x ({db_gain} dB)")
        except ValueError:
            self.add_message_to_queue("Invalid gain value.\n")
            logging.error("Invalid gain value entered.")

    def map_language_for_translation(self, lang_code):
        """Map language codes from SpeechRecognition to those accepted by GoogleTranslator."""
        mapping = {
            'af': 'af', 'sq': 'sq', 'am': 'am', 'ar': 'ar', 'hy': 'hy', 'az': 'az',
            'eu': 'eu', 'be': 'be', 'bn': 'bn', 'bs': 'bs', 'bg': 'bg', 'ca': 'ca',
            'ceb': 'ceb', 'ny': 'ny', 'zh-CN': 'zh-CN', 'zh-TW': 'zh-TW',
            'co': 'co', 'hr': 'hr', 'cs': 'cs', 'da': 'da', 'nl': 'nl', 'en': 'en',
            'en-US': 'en', 'en-GB': 'en', 'eo': 'eo', 'et': 'et', 'tl': 'tl', 'fi': 'fi',
            'fr': 'fr', 'fy': 'fy', 'gl': 'gl', 'ka': 'ka', 'de': 'de', 'el': 'el',
            'gu': 'gu', 'ht': 'ht', 'ha': 'ha', 'he': 'he', 'hi': 'hi', 'hmn': 'hmn',
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

    def toggle_tts(self):
        """Toggle Text-to-Speech functionality."""
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

    async def async_speak_text(self, text, retry_count=3):
        """Asynchronously speak text using edge-tts and play it."""
        for attempt in range(1, retry_count + 1):
            try:
                if not self.tts_enabled.get():
                    logging.debug("TTS is disabled. Skipping speech synthesis.")
                    return
                selected_voice_entry = self.voice_var.get()
                selected_voice_name = selected_voice_entry.split(" (")[0] if " (" in selected_voice_entry else selected_voice_entry
                logging.debug(f"Selected voice entry: '{selected_voice_entry}' parsed to voice name: '{selected_voice_name}'")
                selected_voice = next(
                    (voice for voice in self.edge_tts_voices if self.strip_voice_prefix(voice['Name']) == selected_voice_name),
                    None
                )
                if not selected_voice:
                    error_message = f"Selected voice '{selected_voice_name}' not found."
                    self.add_message_to_queue(error_message + "\n")
                    logging.error(error_message)
                    return
                voice = selected_voice['ShortName']
                logging.debug(f"Using voice: {voice}")
                communicate = edge_tts.Communicate(text, voice=voice)
                mp3_buffer = io.BytesIO()
                async for chunk in communicate.stream():
                    if chunk["type"] == "audio":
                        mp3_buffer.write(chunk["data"])
                if mp3_buffer.tell() == 0:
                    error_message = "No audio data received from TTS service."
                    self.add_message_to_queue(error_message + "\n")
                    logging.error(error_message)
                    raise ValueError("No audio data received.")
                mp3_buffer.seek(0)
                try:
                    audio = AudioSegment.from_file(mp3_buffer, format="mp3")
                    wav_buffer = io.BytesIO()
                    audio.export(wav_buffer, format="wav")
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

    def speak_text(self, text):
        """Speak text using TTS if enabled."""
        if self.tts_enabled.get() and hasattr(self, 'tts_loop') and hasattr(self, 'edge_tts_voices'):
            try:
                coro = self.async_speak_text(text)
                asyncio.run_coroutine_threadsafe(coro, self.tts_loop)
                logging.debug(f"Scheduled TTS for text: {text}")
            except Exception as e:
                self.add_message_to_queue(f"Error scheduling TTS: {e}\n")
                logging.error(f"Error scheduling TTS: {e}")

    def get_output_devices(self):
        """Return a list of available output devices."""
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

    def list_edge_tts_voices(self):
        """Fetch available TTS voices and update the voice combobox."""
        async def fetch_voices():
            try:
                voices = await edge_tts.list_voices()
                self.edge_tts_voices = voices
                voice_names = []
                for voice in voices:
                    stripped_name = self.strip_voice_prefix(voice['Name'])
                    locale_code = voice['Locale']
                    language_name = self.get_full_language_name(locale_code)
                    display_name = f"{stripped_name} ({language_name})"
                    voice_names.append(display_name)
                    logging.debug(f"Processed voice: '{stripped_name}' with language: '{language_name}'")
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

    def update_voice_combobox(self, voice_names):
        """Update the voice combobox with the available voices."""
        try:
            self.voice_combobox['values'] = voice_names
            if voice_names:
                self.voice_combobox.set(voice_names[0])
                self.voice_combobox.config(state="readonly")
                self.add_message_to_queue("Select a voice from the combobox.\n")
                logging.info("Voice selection updated.")
            else:
                self.voice_combobox.set("No voices available")
                self.voice_combobox.config(state="disabled")
        except Exception as e:
            self.add_message_to_queue(f"Error updating voice combobox: {e}\n")
            logging.error(f"Error updating voice combobox: {e}")

    def read_wav(self, filename):
        """Read a WAV file and return its sample rate and data."""
        fs, data = read(filename)
        if data.dtype != np.float32:
            max_val = np.max(np.abs(data))
            if max_val == 0:
                max_val = 1
            data = data.astype(np.float32) / max_val
        return fs, data

    def stop_tts_loop(self):
        """Stop the TTS asyncio loop gracefully."""
        try:
            if hasattr(self, 'tts_loop') and self.tts_loop.is_running():
                self.tts_loop.call_soon_threadsafe(self.tts_loop.stop)
                self.tts_thread.join(timeout=1)
                logging.info("TTS event loop stopped.")
        except Exception as e:
            self.add_message_to_queue(f"Error stopping TTS loop: {e}\n")
            logging.error(f"Error stopping TTS loop: {e}")

    def update_spoken_language(self, *args):
        """Update the current spoken language when selection changes."""
        try:
            self.current_spoken_language = self.languages.get(self.spoken_language_var.get(), "en")
            logging.debug(f"Spoken language updated to: {self.current_spoken_language}")
        except Exception as e:
            self.add_message_to_queue(f"Error updating spoken language: {e}\n")
            logging.error(f"Error updating spoken language: {e}")

    def update_target_language(self, *args):
        """Update the current target language when selection changes."""
        try:
            self.current_target_language = self.languages.get(self.target_language_var.get(), "en")
            logging.debug(f"Target language updated to: {self.current_target_language}")
        except Exception as e:
            self.add_message_to_queue(f"Error updating target language: {e}\n")
            logging.error(f"Error updating target language: {e}")

    def disable_buffer_size_control(self):
        """Disable the buffer size slider during audio capture."""
        try:
            self.buffer_size_slider.config(state='disabled')
            logging.debug("Buffer size control disabled during audio capture.")
        except Exception as e:
            self.add_message_to_queue(f"Error disabling buffer size control: {e}\n")
            logging.error(f"Error disabling buffer size control: {e}")

    def enable_buffer_size_control(self):
        """Enable the buffer size slider after audio capture."""
        try:
            self.buffer_size_slider.config(state='normal')
            logging.debug("Buffer size control enabled after stopping audio capture.")
        except Exception as e:
            self.add_message_to_queue(f"Error enabling buffer size control: {e}\n")
            logging.error(f"Error enabling buffer size control: {e}")

    def strip_voice_prefix(self, voice_name):
        """Remove a redundant prefix from the voice name."""
        prefix = "Microsoft Server Speech Text to Speech Voice "
        if voice_name.lower().startswith(prefix.lower()):
            stripped_name = voice_name[len(prefix):].strip("'\" ")
            logging.debug(f"Stripped voice name: '{stripped_name}' from original '{voice_name}'")
            return stripped_name
        logging.debug(f"No prefix found to strip for voice name: '{voice_name}'")
        return voice_name

# Start the application
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
