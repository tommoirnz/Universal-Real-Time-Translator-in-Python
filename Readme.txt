
You can either have a micophone or read from a data stream in the PC (ie a file playing or video etc). You select the input device. Select the source and the destination language.
So for example French to English. If you require the translation spoken you must enable the spoken text to speech and select a suitable voice. You may have to load the foreign voice on your PC.
If you use say an English voice on an English to French translation it will come out all Franglais which can be quite amusing!
You can save a transcript of the translation in text afterwards. It has a buffer, best not to change it to begin with. Make it bigger and the delay becomes longer (latency).
It uses Google deep learning and translation in Python. It is modelled a bit on Star Trek Universal translator but so far the auto detect language doesn't work that well
so I had to put up with defining the source and destination languages. It is a bit like some apps for phones but runs on a PC continuously.
You don't have to wait and then press a button to translate. You might want to use earphones if you are using a microphone otherwise with an external mic it hears itself 
and you get an echo around effect where it keeps repeating itself!

Written by ChatGPT o1-mini which I found the best to date of the AI LL models for programming (though I have just scratched the surface). You will need FFMPEG (free download) installed on your pc and important - the path must be entered so that it runs if you type ffmpeg at the command prompt of the pc. Download the Windows version. I have not tested this in Linux or other OS's.


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

Note latest update reads text files and epub files.

Tom Moir
tomspeechnz@gmail.com
