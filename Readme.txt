This is a comprehensive real‐time language translator application built in Python. The code combines multiple advanced features and libraries to create a full‐featured GUI application that:

Captures Audio & Recognizes Speech:
It uses the sounddevice module to capture audio from the microphone, processes the audio data (with gain control and buffering), and employs the speech_recognition library (via Google’s speech API) to convert spoken language into text. It also includes logic to detect silence and manage overlapping audio segments.

Translates Text:
The application uses the deep_translator package (specifically, GoogleTranslator) to translate recognized or manually entered text between languages. It also implements an LRU cache (using an OrderedDict) to store translation results for efficiency.

Text-to-Speech (TTS) Integration:
With the help of edge_tts, the app converts translated text into speech. It manages asynchronous TTS operations with Python’s asyncio and uses the pydub library to handle audio format conversion (from MP3 to WAV) for playback with sounddevice.

Graphical User Interface (GUI):
Built with Tkinter (along with ttk for modern widgets), the GUI supports multiple functionalities including:

Displaying real-time recognized and translated text.
Offering controls for audio capture, translation speed, buffer size, and microphone gain.
Allowing users to load text from files (both EPUB and TXT) or enter text manually.
Providing sliders to control navigation within the text and dynamic font scaling.
A dedicated translation window with options for TTS voice selection and output device configuration.
Minimizing the application to the system tray using pystray.
Additional Functionalities:

Batch Translation: The code supports translating an entire document in segments with a progress indicator.
Error Logging: Detailed logging is implemented throughout (using the logging module) to record events, errors, and debugging information into a file located in the user’s home directory.
Threading & Concurrency: Background tasks such as audio processing, TTS operations, and batch translations are managed using threads and a thread pool (ThreadPoolExecutor).
Code Structure & Design:
The main functionality is encapsulated in the TranslatorApp class, which organizes the GUI, audio processing, translation, and TTS functionalities. The code also includes various utility functions for tasks like splitting and merging text segments, handling file reading (including EPUB parsing via ebooklib and BeautifulSoup), and managing dynamic UI updates.

Overall, this code is designed to be a robust, feature-rich language translator that supports both real-time audio translation and manual text input, complete with an intuitive user interface and advanced audio and text processing capabilities.





You can either have a micophone or read from a data stream in the PC (ie a file playing or video etc). You select the input device. Select the source and the destination language.
So for example French to English. If you require the translation spoken you must enable the spoken text to speech and select a suitable voice. You may have to load the foreign voice on your PC.
If you use say an English voice on an English to French translation it will come out all Franglais which can be quite amusing!
You can save a transcript of the translation in text afterwards. It has a buffer, best not to change it to begin with. Make it bigger and the delay becomes longer (latency).
It uses Google deep learning and translation in Python. It is modelled a bit on Star Trek Universal translator but so far the auto detect language doesn't work that well
so I had to put up with defining the source and destination languages. It is a bit like some apps for phones but runs on a PC continuously.
You don't have to wait and then press a button to translate. You might want to use earphones if you are using a microphone otherwise with an external mic it hears itself 
and you get an echo around effect where it keeps repeating itself!

Written by ChatGPT o1-mini which I found the best to date of the AI LL models for programming (though I have just scratched the surface). Update - later I found o3-mini even better still!  You will need FFMPEG (free download) installed on your pc and important - the path must be entered so that it runs if you type ffmpeg at the command prompt of the pc. Download the Windows version. I have not tested this in Linux or other OS's.


https://www.ffmpeg.org/download.html

Search “Advanced system settings” in the Windows search bar.
Click the “Environment Variables” button.
Select “Path” from the list of system variables and click “Edit.”
Click “New” and add the path to your ffmpeg folder, then click “OK.”

If it doesn't run when you type ffmpeg at the command prompt the path isn't set up properly. Remember and reboot after setting the path. If you don't install ffmpeg it still run but you won't be able to get sound out of the text to speech. You can use the text based input and output for example. 

https://www.youtube.com/watch?v=8OCFdHo2zvg

a video of it working!


Requirements file is requirements.txt
use.  pip install -r requirements.txt

Note latest update reads text files and epub files. I attach a couple of open source book extracts to test out the file read and experimentation. If you compile this with auto-py-to-exe you need the icon.ico file to add.
Also when running the .exe if compiled you need the icon in the same directory or the minimize to tray will not work. Same goes for the logo ie logo.jpg or no logo will appear on top right hand side op root window.

Tom Moir
tomspeechnz@gmail.com
