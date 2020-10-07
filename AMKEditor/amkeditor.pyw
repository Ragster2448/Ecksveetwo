# ------------------------------------------------------------------------- #
# --- AMK Editor 1.1.1 ---------------------------------------------------- #
# --- Program by Ragster -------------------------------------------------- #
# --- A tool for creating and editing lip-sync animations in Xenoverse. --- #
# ------------------------------------------------------------------------- #

import os
import sys
from io import BytesIO
from copy import deepcopy
from struct import pack, unpack
import webbrowser
import wave
import pyaudio
import threading
import tkinter as tk
import tkinter.messagebox as messagebox
import tkinter.filedialog as filedialog
from PIL import ImageTk, Image
from functools import partial

import amkimage

pya = pyaudio.PyAudio()

# ---------------------------- #
# --- Dictionary (English) --- #
# ---------------------------- #

txt = {
    'TITLE': 'AMK Editor',
    'ABOUT': 'AMK Editor 1.1.1\nProgram by Ragster',
    'ANI_ADD': 'Add animation',
    'ANI_CLR': 'Clear animation',
    'ANI_DEL': 'Delete animation',
    'ANI_DUP': 'Duplicate animation',
    'ANI_MUP': 'Move animation up',
    'ANI_MDN': 'Move animation down',
    'ANI_NEW': 'NewAnimation',
    'ANI_WAV': 'Assign WAV file...',
    'ANI_WVR': 'Remove WAV file',
    'BUT_LEN': 'Length from WAV',
    'DIA_MOD': 'There are some unsaved changes to the current file. Do you want to continue?',
    'DIA_NOT': 'The selected file is not a recognized file type.',
    'DIA_SAV': 'File saved successfully.',
    'DIA_WVE': 'Supported WAV encodings include 8-bit PCM, 16-bit PCM, and 32-bit PCM.',
    'DIA_WVF': 'The selected folder does not contain any valid WAV files.',
    'DIA_WVG': 'Successfully loaded {good} WAV files. Failed to load {bad} WAV files.',
    'DIA_WVN': 'Please ensure that the WAV file names correspond with the animation names.',
    'DIA_WVS': 'The selected file is too large to open! WAV files cannot exceed ~68.25 seconds. What, are you animating a short story?',
    'FIL_ALL': 'All files',
    'FIL_AMK': 'AMK files',
    'FIL_WAV': 'WAV files',
    'LAB_ANI': 'Animation List',
    'LAB_KEY': 'Key Editor',
    'LAB_LEN': 'Length:',
    'LAB_PRE': 'Preview',
    'MNB_FIL': 'File',
    'MNB_HLP': 'Help',
    'MNI_ABT': 'About...',
    'MNI_DOC': 'Documentation...',
    'MNI_EXT': 'Exit',
    'MNI_NEW': 'New',
    'MNI_OPN': 'Open...',
    'MNI_SAV': 'Save',
    'MNI_SVA': 'Save as...',
    'MNI_WAV': 'Open WAV directory...'
}

kyn = (
    'Default',
    'A (Normal)',
    'I (Normal)',
    'U (Normal)',
    'E (Normal)',
    'O (Normal)',
    'Default (2)',
    'A (Accent)',
    'I (Accent)',
    'U (Accent)',
    'E (Accent)',
    'O (Accent)'
)

# ------------------------ #
# --- Global Variables --- #
# ------------------------ #

# The last directory opened in a filedialog.
# This is updated every time a file is opened/saved.
lastDir = os.getcwd()

# Holds the link to the documentation.
docLink = 'https://docs.google.com/document/d/1zc6bVrk99gtDwPuA5HNMXWYh9nNTc2svaijshC6A83s'

# The currently loaded AMK file.
amkFile = ''

# List that stores AMK data.
#  amkData structure: [[aniData], [aniData], [aniData], ...]
#  aniData structure: [name, length, wavFile, [wavData], [keyList]]
#  wavData structure: [(x, y), (x, y), (x, y), ...]
#  keyList structure: [[keyData], [keyData], [keyData], ...]
#  keyData structure: [frame number, animation index, accent flag]
amkData = []

# Keeps track of AMK modification for dialog warnings.
amkModified = False

# Associates canvas items with key indexes.
keyItem = []

# Maximum size (in pixels) of a WAV file.
# 16384 pixels is roughly 68.25 seconds long.
wavSize = 16384

# Holds the playback thread.
playback = None

# Playback thread will stop if set to true.
playbackStop = False

# --------------------------- #
# --- Main Window Handler --- #
# --------------------------- #

class Editor:
    def __init__(self, parent):

        # Create image resources
        self.img = {
            'LOAD': ImageTk.PhotoImage(file=BytesIO(amkimage.get('LOAD'))),
            'PLAY': ImageTk.PhotoImage(file=BytesIO(amkimage.get('PLAY'))),
            'ADD': ImageTk.PhotoImage(file=BytesIO(amkimage.get('ADD'))),
            'DEL': ImageTk.PhotoImage(file=BytesIO(amkimage.get('DEL'))),
            'P000': ImageTk.PhotoImage(file=BytesIO(amkimage.get('P000'))),
            'P001': ImageTk.PhotoImage(file=BytesIO(amkimage.get('P001'))),
            'P002': ImageTk.PhotoImage(file=BytesIO(amkimage.get('P002'))),
            'P003': ImageTk.PhotoImage(file=BytesIO(amkimage.get('P003'))),
            'P004': ImageTk.PhotoImage(file=BytesIO(amkimage.get('P004'))),
            'P005': ImageTk.PhotoImage(file=BytesIO(amkimage.get('P005'))),
            'P006': ImageTk.PhotoImage(file=BytesIO(amkimage.get('P006'))),
            'P007': ImageTk.PhotoImage(file=BytesIO(amkimage.get('P007'))),
            'P008': ImageTk.PhotoImage(file=BytesIO(amkimage.get('P008'))),
            'P009': ImageTk.PhotoImage(file=BytesIO(amkimage.get('P009'))),
            'P010': ImageTk.PhotoImage(file=BytesIO(amkimage.get('P010'))),
            'P011': ImageTk.PhotoImage(file=BytesIO(amkimage.get('P011')))
        }

        # Window info
        self.parent = parent
        parent.title(txt['TITLE'])
        parent.minsize(800, 600)
        parent.protocol('WM_DELETE_WINDOW', self.menuExit)
        parent.rowconfigure(0, weight=1)
        parent.rowconfigure(1, weight=1)
        parent.columnconfigure(0, weight=1)
        parent.columnconfigure(1, weight=1)
        parent.columnconfigure(2, weight=1)

        # Menu bar
        menu = tk.Menu(parent)
        parent.config(menu=menu)

        # Menu bar -> File menu
        menuFile = tk.Menu(menu, tearoff=0)
        menuFile.add_command(label=txt['MNI_NEW'], command=self.menuNew)
        menuFile.add_command(label=txt['MNI_OPN'], command=self.menuOpen)
        menuFile.add_command(label=txt['MNI_SAV'], command=self.menuSave)
        menuFile.add_command(label=txt['MNI_SVA'], command=self.menuSaveAs)
        menuFile.add_separator()
        menuFile.add_command(label=txt['MNI_WAV'], command=self.menuWAV)
        menuFile.add_separator()
        menuFile.add_command(label=txt['MNI_EXT'], command=self.menuExit)
        menu.add_cascade(label=txt['MNB_FIL'], menu=menuFile)

        # Menu bar -> Help menu
        menuHelp = tk.Menu(menu, tearoff=0)
        menuHelp.add_command(label=txt['MNI_ABT'], command=self.menuAbout)
        menuHelp.add_command(label=txt['MNI_DOC'], command=self.menuDoc)
        menu.add_cascade(label=txt['MNB_HLP'], menu=menuHelp)

        # Animation frame
        aniFrame = tk.LabelFrame(parent, text=txt['LAB_ANI'], highlightcolor='#F0F0F0', highlightthickness=3)
        aniFrame.grid(row=0, rowspan=2, column=0, sticky='nsew')
        aniFrame.rowconfigure(0, weight=1)
        aniFrame.columnconfigure(0, weight=1)

        self.aniList = tk.Listbox(aniFrame, selectmode='single', exportselection=False)
        self.aniList.grid(row=0, column=0, sticky='nsew')

        self.aniScroll = tk.Scrollbar(aniFrame)
        self.aniScroll.grid(row=0, column=1, sticky='nsew')
        self.aniScroll.config(command=self.aniList.yview)
        self.aniList.config(yscrollcommand=self.aniScroll.set)

        self.aniName = tk.StringVar()
        self.aniEntry = tk.Entry(aniFrame, textvariable=self.aniName, state='disabled')
        self.aniEntry.grid(row=1, column=0, columnspan=2, sticky='nsew')

        # Preview frame
        preFrame = tk.LabelFrame(parent, text=txt['LAB_PRE'], highlightcolor='#F0F0F0', highlightthickness=3)
        preFrame.grid(row=0, rowspan=2, column=1, columnspan=2, sticky='nsew')
        preFrame.rowconfigure(0, weight=1)
        preFrame.columnconfigure(0, weight=1)

        self.preImage = tk.Label(preFrame, image=self.img['P000'])
        self.preImage.grid(sticky='nsew')

        # Audio frame
        audFrame = tk.LabelFrame(parent, text=txt['LAB_KEY'], highlightcolor='#F0F0F0', highlightthickness=3)
        audFrame.grid(row=2, column=0, columnspan=3, sticky='nesw')
        audFrame.columnconfigure(0, weight=1)

        # Audio toolbar
        audBar = tk.Frame(audFrame, highlightcolor='#F0F0F0', highlightthickness=2)
        audBar.grid(row=0, column=0, sticky='nsew')

        self.audBarOpen = tk.Button(audBar, image=self.img['LOAD'], command=self.audOpen, state='disabled')
        self.audBarOpen.pack(side='left')

        self.audBarPlay = tk.Button(audBar, image=self.img['PLAY'], command=self.audPlay, state='disabled')
        self.audBarPlay.pack(side='left')

        self.audBarAdd = tk.Button(audBar, image=self.img['ADD'], command=self.keyAdd, state='disabled')
        self.audBarAdd.pack(side='left')

        self.audBarDel = tk.Button(audBar, image=self.img['DEL'], command=self.keyDel, state='disabled')
        self.audBarDel.pack(side='left')

        self.audBarKey = tk.StringVar()
        self.audBarKey.set(kyn[0])
        self.audBarOption = tk.OptionMenu(audBar, self.audBarKey, *kyn, command=self.keyChange)
        self.audBarOption.config(width=10, state='disabled')
        self.audBarOption.pack(side='left')

        self.audBarPos = tk.IntVar()
        self.audBarFrame = tk.Spinbox(audBar, textvariable=self.audBarPos, width=5, from_=0, to=int(wavSize/4)-1, highlightcolor='#F0F0F0', highlightthickness=5, command=self.keyFrame, state='disabled')
        self.audBarFrame.pack(side='left')

        self.audBarButton = tk.Button(audBar, text=txt['BUT_LEN'], command=self.audLengthWAV, state='disabled')
        self.audBarButton.pack(side='right')

        self.audBarLength = tk.IntVar()
        self.audBarEntry = tk.Spinbox(audBar, textvariable=self.audBarLength, width=5, from_=0, to=int(wavSize/4)-1, highlightcolor='#F0F0F0', highlightthickness=5, command=self.audLength, state='disabled')
        self.audBarEntry.pack(side='right')
        audBarLabel = tk.Label(audBar, text=txt['LAB_LEN'])
        audBarLabel.pack(side='right')

        # Audio timeline
        self.audTime = tk.Canvas(audFrame, bg='gainsboro', width=wavSize, height=20, scrollregion=(0, 0, 0, 0))
        self.audTime.grid(row=1, column=0, sticky='nsew')
        self.audTime.create_rectangle(1, 1, wavSize-2, 18, fill='white', outline='white')
        for i in range(0, wavSize, 4):
            self.audTime.create_line(i, 16-(i%240 == 0)-(i%120 == 0)-(i%60 == 0), i, 20, fill='gray')
            if (i == 0):
                self.audTime.create_text(i+3, 1, anchor='nw', font=("Purisa", 7), text='0')
            elif (i%60 == 0):
                self.audTime.create_text(i, 1, anchor='n', font=("Purisa", 7), text=str(int(i/4)))

        # Audio waveform
        self.audWave = tk.Canvas(audFrame, bg='gainsboro', width=wavSize, height=100, scrollregion=(0, 0, 0, 0))
        self.audWave.grid(row=2, column=0, sticky='nsew')
        self.audWave.create_line(0, 9, 0, 99, fill='limegreen', arrow='first', arrowshape=(-8, -8, 4), tags='marker')

        # Audio scrollbar
        self.audScroll = tk.Scrollbar(audFrame, orient='horizontal', command=self.audScrollSync)
        self.audScroll.grid(row=3, column=0, sticky='nsew')
        self.audTime.config(xscrollcommand=self.audScroll.set)
        self.audWave.config(xscrollcommand=self.audScroll.set)

        # Set bindings
        self.aniList.bind('<<ListboxSelect>>', self.updateAud, add='+')
        self.aniList.bind('<<ListboxSelect>>', self.updateKey, add='+')
        self.aniList.bind('<Button-3>', self.aniMenu)
        self.aniEntry.bind('<Return>', self.aniRename)
        self.audBarFrame.bind('<Return>', self.keyFrame)
        self.audBarEntry.bind('<Return>', self.audLength)
        self.audWave.bind('<Button-1>', self.audMarker)
        self.audWave.bind('<B1-Motion>', self.audMarker)

        # 'Open with...' handler
        if len(sys.argv) > 1:
            lastDir = os.path.dirname(sys.argv[1])
            if self.loadAMK(path=sys.argv[1]):
                self.updateAni()
                self.updateAud()
                self.updateKey()

    # ---------------------- #
    # --- Load Functions --- #
    # ---------------------- #

    # Load an AMK file.
    def loadAMK(self, path):
        global amkFile
        global amkData
        global amkModified
        if os.path.getsize(path) < 32:
            return -1
        with open(path, mode='rb') as file:
            amk = file.read()
            amkHead = unpack('8I', amk[:32])
            if amkHead[0] != 1263354147:
                file.close()
                return -2
            amkFile = path
            amkData.clear()
            amkModified = False
            for i in range(amkHead[5]):
                p = 32+i*16
                aniHead = unpack('4I', amk[p:p+16])
                p = amkHead[7]+i*32
                aniName = ''
                for j in range(32):
                    if amk[p+j] == 0:
                        break
                    aniName += chr(amk[p+j])
                aniData = [aniName, aniHead[0], -1, [], []]
                for k in range(aniHead[1]):
                    p = aniHead[3]+k*4
                    aniData[4].append(list(unpack('HBB', amk[p:p+4])))
                amkData.append(aniData)
            file.close()
            return 0

    # Load a WAV file.
    def loadWAV(self, path, index):
        global amkData
        try:
            wav = wave.open(path, mode='rb')
        except:
            return -1
        wavInfo = wav.getparams()
        wavData = wav.readframes(-1)
        if wavInfo[1] != 1 and wavInfo[1] != 2 and wavInfo[1] != 4:
            wav.close()
            return -2
        wavLength = int(240*wavInfo[3]/wavInfo[2])
        if wavLength >= wavSize:
            wav.close()
            return -3
        amkData[index][2] = wav
        amkData[index][3].clear()

        # 8-bit Unsigned
        if wavInfo[1] == 1:
            for i in range(wavLength):
                wavSample = int(wavInfo[3]*i/wavLength)*wavInfo[0]*wavInfo[1]
                amkData[index][3].append((i, unpack('B', wavData[wavSample:wavSample+1])[0]/128*50))

        # 16-bit Signed
        if wavInfo[1] == 2:
            for i in range(wavLength):
                wavSample = int(wavInfo[3]*i/wavLength)*wavInfo[0]*wavInfo[1]
                amkData[index][3].append((i, 50+(unpack('h', wavData[wavSample:wavSample+2])[0]/32768*50)))

        # 32-bit Signed
        if wavInfo[1] == 4:
            for i in range(wavLength):
                wavSample = int(wavInfo[3]*i/wavLength)*wavInfo[0]*wavInfo[1]
                amkData[index][3].append((i, 50+(unpack('i', wavData[wavSample:wavSample+4])[0]/2147483648*50)))

        return 0

    # ---------------------- #
    # --- Main Functions --- #
    # ---------------------- #

    # Use this function to check for modification.
    def check(self):
        global amkModified
        return (amkModified == False or messagebox.askokcancel(title=txt['TITLE'], message=txt['DIA_MOD']))

    # 'Update' functions below the one called should always be called afterward.

    # Use this function after modifying animations.
    def updateAni(self, event=None):
        pos = self.aniScroll.get()[0]
        self.aniList.select_clear(first=0, last='end')
        self.aniList.delete(0, 'end')
        for i in range(len(amkData)):
            if amkData[i][0] != '':
                self.aniList.insert('end', str(i).zfill(3)+'. '+amkData[i][0])
                if amkData[i][2] != -1:
                    self.aniList.itemconfig(i, {'fg': 'blue'})
            else:
                self.aniList.insert('end', str(i).zfill(3)+'. EMPTY')
                self.aniList.itemconfig(i, {'fg': 'orange'})
        self.aniList.yview_moveto(pos)

    # Use this function after changing animations.
    def updateAud(self, event=None):
        index = self.aniList.curselection()
        pos = self.audScroll.get()[0]
        self.audBarPlay.config(state='disabled')
        self.audBarButton.config(state='disabled')
        self.audWave.delete('wave')
        self.audWave.coords('marker', 0, 9, 0, 99)
        if index:
            self.aniEntry.config(state='normal')
            self.aniName.set(amkData[index[0]][0])
            self.audBarOpen.config(state='normal')
            self.audBarAdd.config(state='normal')
            self.audBarEntry.config(state='normal')
            self.audBarLength.set(amkData[index[0]][1])
            self.audTime.config(scrollregion=(0, 0, amkData[index[0]][1]*4+1, 0))
            self.audWave.config(scrollregion=(0, 0, amkData[index[0]][1]*4+1, 0))
            wavLength = len(amkData[index[0]][3])
            if wavLength > 0:
                self.audBarPlay.config(state='normal')
                self.audBarButton.config(state='normal')
                self.audWave.create_rectangle(1, 1, wavLength-2, 98, fill='white', outline='white', tags='wave')
                self.audWave.create_line(0, 50, wavLength-1, 50, fill='gray', tags='wave')
                self.audWave.create_line(amkData[index[0]][3], fill='blue', tags='wave')
                self.audWave.tag_raise('marker')
        else:
            self.aniName.set('')
            self.aniEntry.config(state='disabled')
            self.audBarOpen.config(state='disabled')
            self.audBarAdd.config(state='disabled')
            self.audBarLength.set(0)
            self.audBarEntry.config(state='disabled')
            self.audTime.config(scrollregion=(0, 0, 0, 0))
            self.audWave.config(scrollregion=(0, 0, 0, 0))
        self.audTime.xview_moveto(pos)
        self.audWave.xview_moveto(pos)

    # Use this function after modifying keys.
    def updateKey(self, event=None):
        global keyItem
        keyItem.clear()
        index = self.aniList.curselection()
        self.preImage.config(image=self.img['P000'])
        self.audTime.delete('key')
        self.audTime.delete('end')
        self.audBarDel.config(state='disabled')
        self.audBarKey.set(kyn[0])
        self.audBarOption.config(state='disabled')
        self.audBarPos.set(0)
        self.audBarFrame.config(state='disabled')
        if index:
            for keyData in amkData[index[0]][4]:
                pos = keyData[0]*4
                key = self.audTime.create_line(pos, 1, pos, 19, fill='darkred', activewidth=3, tags='key')
                self.audTime.tag_bind(key, '<Button-1>', partial(self.keySelect, key=key))
                self.audTime.tag_bind(key, '<B1-Motion>', partial(self.keyMove, key=key))
                self.audTime.tag_bind(key, '<ButtonRelease-1>', partial(self.keyDrop, key=key))
                keyItem.append(key)
            pos = amkData[index[0]][1]*4
            self.audTime.create_line(pos, 1, pos, 19, fill='black', tags='end')

    # -------------------------- #
    # --- Menu Bar Functions --- #
    # -------------------------- #

    # Create a new file.
    def menuNew(self):
        global amkFile
        global amkData
        global amkModified
        if self.check():
            amkFile = ''
            amkData.clear()
            amkModified = False
            self.updateAni()
            self.updateAud()
            self.updateKey()

    # Open an existing file.
    def menuOpen(self):
        global lastDir
        if self.check():
            fileName = filedialog.askopenfilename(initialdir=lastDir, title=txt['TITLE'], filetypes=((txt['FIL_AMK'], '*.amk'), (txt['FIL_ALL'], '*.*')))
            if fileName != '':
                lastDir = os.path.dirname(fileName)
                if self.loadAMK(path=fileName) == 0:
                    self.updateAni()
                    self.updateAud()
                    self.updateKey()
                else:
                    messagebox.showerror(title=txt['TITLE'], message=txt['DIA_NOT'])

    # Save the current file.
    def menuSave(self):
        global amkModified
        if os.path.exists(amkFile):
            amkModified = False
            with open(amkFile, mode='wb') as file:
                aniSize = len(amkData)
                file.write(pack('8I', 1263354147, 32, 0, 1, 4, aniSize, 32, 0))
                for i in range(aniSize):
                    file.write(pack('4I', 0, 0, 0, 0))
                for i in range(aniSize):
                    keySize = len(amkData[i][4])
                    if keySize > 0:
                        p = file.tell()
                        file.seek(32+i*16)
                        file.write(pack('4I', amkData[i][1], keySize, 1, p))
                        file.seek(p)
                        for j in range(keySize):
                            file.write(pack('HBB', amkData[i][4][j][0], amkData[i][4][j][1], amkData[i][4][j][2]))
                p = file.tell()
                file.seek(28)
                file.write(pack('I', p))
                file.seek(p)
                for i in range(aniSize):
                    file.write(pack('32s', bytearray(amkData[i][0], 'utf8')))
                file.close()
            messagebox.showinfo(title=txt['TITLE'], message=txt['DIA_SAV'])
        else:
            self.menuSaveAs()

    # Save the current file to a new file.
    def menuSaveAs(self):
        global lastDir
        global amkFile
        fileName = filedialog.asksaveasfilename(initialdir=lastDir, title=txt['TITLE'], filetypes=((txt['FIL_AMK'], '*.amk'), (txt['FIL_ALL'], '*.*')))
        if fileName != '':
            if fileName[-4:] != '.amk':
                fileName += '.amk'
            lastDir = os.path.dirname(fileName)
            open(fileName, mode='wb').close()
            amkFile = fileName
            self.menuSave()

    # Load multiple WAV files from the chosen directory.
    def menuWAV(self):
        global lastDir
        global amkData
        dirName = filedialog.askdirectory()
        if dirName != '':
            lastDir = dirName
            fileStatus = [0, 0]
            directory = os.fsencode(dirName)
            for file in os.listdir(directory):
                fileName = os.fsdecode(file)
                if not fileName.endswith('.wav'):
                    continue
                for index in range(len(amkData)):
                    if fileName[:-4] == amkData[index][0]:
                        break
                else:
                    fileStatus[1] += 1
                    continue
                if self.loadWAV(path=dirName+'/'+fileName, index=index) == 0:
                    fileStatus[0] += 1
                else:
                    fileStatus[1] += 1
            if fileStatus[0] > 0:
                self.updateAni()
                self.updateAud()
                self.updateKey()
                if fileStatus[1] > 0:
                    messagebox.showinfo(title=txt['TITLE'], message=txt['DIA_WVG'].format(good=fileStatus[0], bad=fileStatus[1])+'\n'+txt['DIA_WVN']+'\n'+txt['DIA_WVE'])
                else:
                    messagebox.showinfo(title=txt['TITLE'], message=txt['DIA_WVG'].format(good=fileStatus[0], bad=fileStatus[1]))
            else:
                messagebox.showerror(title=txt['TITLE'], message=txt['DIA_WVF']+'\n'+txt['DIA_WVN']+'\n'+txt['DIA_WVE'])

    # Exit the program.
    def menuExit(self):
        if self.check():
            playbackStop = True
            root.destroy()

    # Display program information.
    def menuAbout(self):
        messagebox.showinfo(title=txt['TITLE'], message=txt['ABOUT'])

    # Display program documentation.
    def menuDoc(self):
        webbrowser.open(docLink)

    # --------------------------- #
    # --- Animation Functions --- #
    # --------------------------- #

    # Rename the current animation.
    def aniRename(self, event=None):
        global amkData
        global amkModified
        index = self.aniList.curselection()[0]
        amkData[index][0] = self.aniName.get()[:32]
        self.updateAni()
        self.aniList.select_set(index)
        self.updateAud()
        self.updateKey()
        amkModified = True

    # Create animation pop-up menu.
    def aniMenu(self, event=None):
        if self.aniList['state'] == 'disabled':
            return
        index = self.aniList.nearest(event.y_root-self.aniList.winfo_rooty())
        self.aniList.select_clear(first=0, last='end')
        self.aniList.select_set(first=index)
        self.updateAud()
        self.updateKey()
        menu = tk.Menu(root, tearoff=0)
        menu.add_command(label=txt['ANI_ADD'], command=self.aniAdd)
        menu.add_command(label=txt['ANI_DUP'], command=self.aniDup)
        menu.add_command(label=txt['ANI_CLR'], command=self.aniClr)
        menu.add_command(label=txt['ANI_DEL'], command=self.aniDel)
        menu.add_separator()
        menu.add_command(label=txt['ANI_MUP'], command=self.aniMup)
        menu.add_command(label=txt['ANI_MDN'], command=self.aniMdn)
        menu.add_separator()
        menu.add_command(label=txt['ANI_WAV'], command=self.audOpen)
        menu.add_command(label=txt['ANI_WVR'], command=self.audClose)
        if index == -1:
            menu.entryconfig(txt['ANI_CLR'], state='disabled')
            menu.entryconfig(txt['ANI_DUP'], state='disabled')
            menu.entryconfig(txt['ANI_DEL'], state='disabled')
            menu.entryconfig(txt['ANI_MUP'], state='disabled')
            menu.entryconfig(txt['ANI_MDN'], state='disabled')
            menu.entryconfig(txt['ANI_WAV'], state='disabled')
            menu.entryconfig(txt['ANI_WVR'], state='disabled')
        elif amkData[index][2] == -1:
            menu.entryconfig(txt['ANI_WVR'], state='disabled')
        if index == 0:
            menu.entryconfig(txt['ANI_MUP'], state='disabled')
        if index == self.aniList.size()-1:
            menu.entryconfig(txt['ANI_MDN'], state='disabled')
        try:
            menu.tk_popup(event.x_root, event.y_root)
        finally:
            menu.grab_release()

    # Add a new animation.
    def aniAdd(self):
        global amkData
        global amkModified
        amkData.append([txt['ANI_NEW'], 0, -1, [], []])
        self.updateAni()
        self.aniList.select_set('end')
        self.aniList.see('end')
        self.updateAud()
        self.updateKey()
        amkModified = True

    # Duplicate the selected animation.
    def aniDup(self):
        global amkData
        global amkModified
        index = self.aniList.curselection()[0]
        amkData.append(deepcopy(amkData[index]))
        self.updateAni()
        self.aniList.select_set('end')
        self.aniList.see('end')
        self.updateAud()
        self.updateKey()
        amkModified = True

    # Clear the selected animation.
    def aniClr(self):
        global amkData
        global amkModified
        index = self.aniList.curselection()[0]
        amkData[index][1] = 0
        amkData[index][4].clear()
        self.updateAni()
        self.aniList.select_set(index)
        self.updateAud()
        self.updateKey()
        amkModified = True

    # Delete the selected animation.
    def aniDel(self):
        global amkData
        global amkModified
        index = self.aniList.curselection()[0]
        amkData.pop(index)
        self.updateAni()
        self.aniList.select_set(index)
        self.updateAud()
        self.updateKey()
        amkModified = True

    # Move the selected animation up.
    def aniMup(self):
        global amkData
        global amkModified
        index = self.aniList.curselection()[0]
        amkData[index-1], amkData[index] = amkData[index], amkData[index-1]
        self.updateAni()
        self.aniList.select_set(index-1)
        self.updateAud()
        self.updateKey()
        amkModified = True

    # Move the selected animation down.
    def aniMdn(self):
        global amkData
        global amkModified
        index = self.aniList.curselection()[0]
        amkData[index+1], amkData[index] = amkData[index], amkData[index+1]
        self.updateAni()
        self.aniList.select_set(index+1)
        self.updateAud()
        self.updateKey()
        amkModified = True

    # ----------------------- #
    # --- Audio Functions --- #
    # ----------------------- #

    # Sync the timeline and waveform to the scrollbar.
    def audScrollSync(self, *args):
        self.audTime.xview(*args)
        self.audWave.xview(*args)

    # Move the audio play marker.
    def audMarker(self, event=None):
        global amkData
        index = self.aniList.curselection()
        if index:
            pos = min(max(int(self.audWave.canvasx(event.x_root-self.audWave.winfo_rootx())/4)*4, 0), amkData[index[0]][1]*4)
            self.audWave.coords('marker', pos, 9, pos, 99)

    # Open a WAV file.
    def audOpen(self):
        global lastDir
        fileName = filedialog.askopenfilename(initialdir=lastDir, title=txt['TITLE'], filetypes=((txt['FIL_WAV'], '*.wav'), (txt['FIL_ALL'], '*.*')))
        if fileName != '':
            lastDir = os.path.dirname(fileName)
            index = self.aniList.curselection()[0]
            code = self.loadWAV(path=fileName, index=index)
            if code == 0:
                self.updateAni()
                self.aniList.select_set(index)
                self.updateAud()
                self.updateKey()
            elif code == -3:
                messagebox.showerror(title=txt['TITLE'], message=txt['DIA_WVS'])
            else:
                messagebox.showerror(title=txt['TITLE'], message=txt['DIA_NOT']+'\n'+txt['DIA_WVE'])

    # Remove WAV file association.
    def audClose(self):
        global amkData
        index = self.aniList.curselection()[0]
        amkData[index][2].close()
        amkData[index][2] = -1
        amkData[index][3].clear()
        self.updateAni()
        self.aniList.select_set(index)
        self.updateAud()
        self.updateKey()

    # Play the current WAV file and animation.
    # Stops the playback if it is already playing.
    def audPlay(self):
        global playback
        global playbackStop
        if playback == None or not playback.is_alive():
            index = self.aniList.curselection()[0]
            playback = threading.Thread(target=AudioPlayback, args=(amkData[index][2],))
            playback.start()
        else:
            playbackStop = True

    # Change the current animation's length.
    def audLength(self, event=None):
        global amkData
        global amkModified
        index = self.aniList.curselection()[0]
        try:
            value = int(self.audBarLength.get())
        except:
            root.bell()
        else:
            amkData[index][1] = min(max(value, int(self.audBarEntry.cget('from'))), int(self.audBarEntry.cget('to')))
            self.updateAud()
            self.updateKey()
            amkModified = True

    # Set the current animation's length to the WAV file.
    def audLengthWAV(self, event=None):
        global amkData
        global amkModified
        index = self.aniList.curselection()[0]
        amkData[index][1] = int(len(amkData[index][3])/4)+1
        self.updateAud()
        self.updateKey()
        amkModified = True

    # --------------------- #
    # --- Key Functions --- #
    # --------------------- #

    # Select a key.
    def keySelect(self, event=None, key=None):
        global amkData
        global keyItem
        indexAni = self.aniList.curselection()[0]
        indexKey = keyItem.index(key)
        value = amkData[indexAni][4][indexKey][1]+amkData[indexAni][4][indexKey][2]*6
        self.preImage.config(image=self.img['P'+str(value).zfill(3)])
        self.audBarDel.config(state='normal')
        self.audBarOption.config(state='normal')
        self.audBarKey.set(kyn[value])
        self.audBarFrame.config(state='normal')
        self.audBarPos.set(amkData[indexAni][4][indexKey][0])
        self.audTime.dtag('key', 'select')
        self.audTime.itemconfig('key', width=1, fill='darkred')
        self.audTime.addtag_withtag('select', key)
        self.audTime.itemconfig(key, width=3, fill='red')

    # Move the selected key.
    def keyMove(self, event=None, key=None):
        global amkData
        global keyItem
        indexAni = self.aniList.curselection()[0]
        indexKey = keyItem.index(key)
        pos = min(max(int(self.audTime.canvasx(event.x_root-self.audTime.winfo_rootx())/4)*4, 0), amkData[indexAni][1]*4)
        if not self.audTime.find_enclosed(pos-1, 1, pos+1, 19):
            self.audBarPos.set(int(pos/4))
            self.audTime.coords(key, pos, 1, pos, 19)

    # Apply the moved key's position.
    def keyDrop(self, event=None, key=None):
        global amkData
        global amkModified
        global keyItem
        indexAni = self.aniList.curselection()[0]
        indexKey = keyItem.index(key)
        pos = int(self.audTime.coords(key)[0]/4)
        if pos != amkData[indexAni][4][indexKey][0]:
            keyData = list(amkData[indexAni][4][indexKey])
            amkData[indexAni][4].pop(indexKey)
            keyData[0] = pos
            for index in range(len(amkData[indexAni][4])):
                if amkData[indexAni][4][index][0] > pos:
                    amkData[indexAni][4].insert(index, keyData)
                    break
            else:
                amkData[indexAni][4].append(keyData)
                index = len(amkData[indexAni][4])-1
            self.updateKey()
            self.keySelect(key=keyItem[index])
            amkModified = True

    # Adjust the key's position via the toolbar.
    def keyFrame(self, event=None):
        global amkData
        global amkModified
        global keyItem
        indexAni = self.aniList.curselection()[0]
        indexKey = keyItem.index(self.audTime.find_withtag('select')[0])
        try:
            value = int(self.audBarPos.get())
        except:
            root.bell()
        else:
            pos = min(max(value, 0), amkData[indexAni][1]-1)
            for keyData in amkData[indexAni][4]:
                if keyData[0] == pos:
                    root.bell()
                    return
            else:
                amkData[indexAni][4][indexKey][0] = pos
                self.updateKey()
                self.keySelect(key=keyItem[indexKey])
                amkModified = True

    # Add a new key at the play marker.
    def keyAdd(self):
        global amkData
        global amkModified
        indexAni = self.aniList.curselection()[0]
        pos = int(self.audWave.coords('marker')[0]/4)
        for index in range(len(amkData[indexAni][4])):
            if amkData[indexAni][4][index][0] == pos:
                pos += 1
                continue
            if amkData[indexAni][4][index][0] > pos:
                amkData[indexAni][4].insert(index, [pos, 0, 0])
                break
        else:
            if pos >= amkData[indexAni][1]:
                root.bell()
                return
            else:
                amkData[indexAni][4].append([pos, 0, 0])
                index = len(amkData[indexAni][4])-1
        self.updateKey()
        self.keySelect(key=keyItem[index])
        amkModified = True

    # Delete the selected key.
    def keyDel(self):
        global amkData
        global amkModified
        indexAni = self.aniList.curselection()[0]
        indexKey = keyItem.index(self.audTime.find_withtag('select')[0])
        amkData[indexAni][4].pop(indexKey)
        self.updateKey()
        amkModified = True

    # Change the selected key.
    def keyChange(self, event=None):
        global amkData
        global amkModified
        indexAni = self.aniList.curselection()[0]
        indexKey = keyItem.index(self.audTime.find_withtag('select')[0])
        value = kyn.index(self.audBarKey.get())
        amkData[indexAni][4][indexKey][1] = value%6
        amkData[indexAni][4][indexKey][2] = int(value/6)
        self.updateKey()
        self.keySelect(key=keyItem[indexKey])
        amkModified = True

# ---------------------- #
# --- Audio Playback --- #
# ---------------------- #

class AudioPlayback(threading.Thread):
    def __init__(self, file):
        global playbackStop
        threading.Thread.__init__(self)
        index = editor.aniList.curselection()[0]
        pos = editor.audWave.coords('marker')

        # Disable editor functionality.
        editor.updateKey()
        root.nametowidget(root['menu']).entryconfig(txt['MNB_FIL'], state='disabled')
        root.nametowidget(root['menu']).entryconfig(txt['MNB_HLP'], state='disabled')
        editor.aniList.config(state='disabled')
        editor.aniEntry.config(state='disabled')
        editor.audBarOpen.config(state='disabled')
        editor.audBarAdd.config(state='disabled')
        editor.audBarButton.config(state='disabled')
        editor.audBarEntry.config(state='disabled')
        editor.audTime.config(state='disabled')
        timer = editor.audWave.create_line(pos[0], 1, pos[2], 99, fill='red')

        # Set the preview image to the key before the marker.
        preKey = 0
        marker = int(pos[0]/4)
        for i in range(1, len(amkData[index][4])):
            if amkData[index][4][i][0] > marker:
                value = amkData[index][4][i-1][1]+amkData[index][4][i-1][2]*6
                editor.preImage.config(image=editor.img['P'+str(value).zfill(3)])
                preKey = i
                break

        # Load the WAV file.
        file.setpos(min(max(int(pos[0]*file.getframerate()/240), 0), file.getnframes()-1))
        stream = pya.open(
            format = pya.get_format_from_width(file.getsampwidth()),
            channels = file.getnchannels(),
            rate = file.getframerate(),
            output = True
        )

        # Play the WAV file.
        data = file.readframes(1024)
        while data:
            if playbackStop:
                playbackStop = False
                break
            stream.write(data)
            data = file.readframes(1024)
            move = file.tell()/file.getframerate()*240
            editor.audWave.coords(timer, move, 1, move, 99)
            marker = int(move/4)
            if preKey < len(amkData[index][4]) and amkData[index][4][preKey][0] < marker:
                value = amkData[index][4][preKey][1]+amkData[index][4][preKey][2]*6
                editor.preImage.config(image=editor.img['P'+str(value).zfill(3)])
                preKey += 1

        # Close the WAV file.
        stream.close()

        # Enable editor functionality.
        root.nametowidget(root['menu']).entryconfig(txt['MNB_FIL'], state='normal')
        root.nametowidget(root['menu']).entryconfig(txt['MNB_HLP'], state='normal')
        editor.aniList.config(state='normal')
        editor.aniEntry.config(state='normal')
        editor.audBarOpen.config(state='normal')
        editor.audBarAdd.config(state='normal')
        editor.audBarButton.config(state='normal')
        editor.audBarEntry.config(state='normal')
        editor.audTime.config(state='normal')
        editor.audWave.delete(timer)

# -------------------------- #
# --- Create Main Window --- #
# -------------------------- #

if __name__ == '__main__':
    root = tk.Tk()
    editor = Editor(root)
    root.geometry('800x600')
    root.mainloop()
