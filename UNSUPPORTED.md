# **276** Unsupported File Formats
These formats can still be **identified** by dexvert, just can't be converted into modern ones.



## Executable (17)
Family | Name | Extensions | Notes
------ | ---- | ---------- | -----
executable | a.out Executable | .o | 
executable | AmigaOS Executable |  | 
executable | Atari Control Panel Extension Module | .cpx | [10 sample files](https://telparia.com/fileFormatSamples/executable/atariCPX/)
executable | Atari Executable | .xex | [4 sample files](https://telparia.com/fileFormatSamples/executable/xex/)
executable | Atari ST Executable |  | [11 sample files](https://telparia.com/fileFormatSamples/executable/atariSTExe/)
executable | ELF Executable |  | 
executable | Linux i386 Executable |  | 
executable | Linux OMAGIC Executable |  | 
executable | Linux ZMAGIC Exectutable |  | 
executable | Mach-O m68k Executable |  | 
executable | MacOS PPC PEF Executable |  | 
executable | MIPSL ECOFF Executable |  | 
executable | MS-DOS COM Executable | .com .c0m | [4 sample files](https://telparia.com/fileFormatSamples/executable/com/)
executable | MS-DOS Driver | .sys .drv | 
executable | RISC OS Executable |  | 
executable | SPARC Demand Paged Exe |  | 
executable | Superbase Program | .sbp | 



## Font (19)
Family | Name | Extensions | Notes
------ | ---- | ---------- | -----
font | 3D Construction Kit Font | .3fd | 
font | AmigaOS Outline Font | .font | 
font | Avery Font | .ff1 | 
font | Banner Mania Font | .fnt | [19 sample files](https://telparia.com/fileFormatSamples/font/bannerManiaFont/)
font | Borland Graphics Font | .chr .bgi | 
font | Bradford Font | .bf2 | 
font | Calamus Font | .cfn | [10 sample files](https://telparia.com/fileFormatSamples/font/calamusFont/)
font | Corel Wiffen Font | .wfn | 
font | DynaCADD Vector Font | .fnt | 
font | Envision Publisher Font | .svf | [3 sample files](https://telparia.com/fileFormatSamples/font/envisionPublisherFont/)
font | LaserJet Soft Font | .sfl .sfp .sft | 
font | LinkWay Font | .fmf | 
font | MacOS Font | .fnt | 
font | PrintPartner Font | .font | 
font | Signum Font | .e24 | 
font | TeX Packed Font | .pf | 
font | TheDraw Font | .tdf | [1 sample file](https://telparia.com/fileFormatSamples/font/theDrawFont/) - Bitmap font file used by programs like Neopaint for MSDOS and maybe GEM OS. Fontforge doesn't handle it
font | VFONT Font | .fnt | 
font | WordUp Graphics Toolkit Font | .wfn | 



## Image (23)
Family | Name | Extensions | Notes
------ | ---- | ---------- | -----
image | Atari ST Graph Diagram | .dia | [3 sample files](https://telparia.com/fileFormatSamples/image/atariGraphDiagram/) - No known converter. Atari ST graphing program by Hans-Christoph Ostendorf.
image | AutoCAD Shape | .shx | [6 sample files](https://telparia.com/fileFormatSamples/image/autoCADShape/)
image | AutoSketch Drawing | .skd | [5 sample files](https://telparia.com/fileFormatSamples/image/autoSketchDrawing/)
image | BBC Display RAM Dump |  | [1 sample file](https://telparia.com/fileFormatSamples/image/bbcDisplayRAM/) - While supported by abydos, due to no extension and no magic, it's impossible to detect accurately.
image | DataShow Sprite | .spr | [2 sample files](https://telparia.com/fileFormatSamples/image/dataShowSprite/) - Support for this format coming soon thanks to abydos.
image | [DraftChoice Drawing](http://www.triusinc.com/forums/viewtopic.php?t=11) | .dch | [30 sample files](https://telparia.com/fileFormatSamples/image/draftChoice/)
image | [Draw 256 Image](http://fileformats.archiveteam.org/wiki/Draw256) | .vga | [4 sample files](https://telparia.com/fileFormatSamples/image/draw256/) - Unsupported because .vga ext is too common, no known magic and converters can't be trusted to verify input file is correct before outputting garbage
image | [DrawStudio Drawing](http://fileformats.archiveteam.org/wiki/DrawStudio) | .dsdr | [8 sample files](https://telparia.com/fileFormatSamples/image/drawStudio/) - Amiga program DrawStudio creates these. No known converter. DrawStudio demo available: https://aminet.net/package/gfx/edit/DrawStudioFPU
image | [Facsimile image FORM](http://fileformats.archiveteam.org/wiki/FAXX) | .faxx .fax | [10 sample files](https://telparia.com/fileFormatSamples/image/faxx/) - Support for this format coming soon in abydos.
image | [Fastgraph Pixel Run Format](http://fileformats.archiveteam.org/wiki/PRF_(Fastgraph)) | .prf | [12 sample files](https://telparia.com/fileFormatSamples/image/fastgraphPRF/) - No known converter. IMPROCES (see website) can load these images and save as GIF/PCX but sadly it's a mouse driven interface which dexvert can't automate yet.
image | [FLI Profi](http://fileformats.archiveteam.org/wiki/FLI_Profi) | .fpr .flp | [1 sample file](https://telparia.com/fileFormatSamples/image/fpr/) - Due to no known magic and how recoil2png/view64 will convert ANYTHING, we disable this for now.
image | [GEM Vector Metafile](http://fileformats.archiveteam.org/wiki/GEM_VDI_Metafile) | .gem .gdi | [16 sample files](https://telparia.com/fileFormatSamples/image/gemMetafile/) - Vector file format that could be converted into SVG. abydos is working on adding support for this format.
image | HomeBrew Icon | .hic | [1 sample file](https://telparia.com/fileFormatSamples/image/homeBrewIcon/)
image | [JPEG XL](http://fileformats.archiveteam.org/wiki/JPEG_XL) | .jxl | [8 sample files](https://telparia.com/fileFormatSamples/image/jpegXL/) - Modern format. Pain in the butt to build the JPEG-XL reference package, I started, see overlay/legacy/JPEG-XL but then gave up because meh.
image | KwikDraw Drawing | .kwk | A windows 'object oriented' drawing program. Don't think it was very popular. sandbox/app/KDRAW121.ZIP has the app, works in Win2k, no export ability. Could add a virtual printer driver and then use that to output as PNG.
image | LEONARD'S Sketch Drawing | .ogf | [6 sample files](https://telparia.com/fileFormatSamples/image/leonardsSketchDrawing/) - Fairly obscure CAD type drawing program. Not aware of any drawings that were not those that were included with the program, so format not worth supporting.
image | [Lotus 1-2-3 Chart](http://fileformats.archiveteam.org/wiki/Lotus_1-2-3_Chart) | .pic | [11 sample files](https://telparia.com/fileFormatSamples/image/lotusChart/) - Support for this format coming soon in abydos (partial format spec: https://www.fileformat.info/format/lotuspic/egff.htm)
image | [Mean Streets MLDF File](http://fileformats.archiveteam.org/wiki/MLDF) | .mld | [32 sample files](https://telparia.com/fileFormatSamples/image/mldf/) - Image file from Mean Streets game. IFF format FORM with MLDF BMHD. Support for this format coming soon in abydos.
image | Micro Illustrator | .mic | [1 sample file](https://telparia.com/fileFormatSamples/image/microIllustrator/) - NOT the same as image/mil Micro Illustrator. Sadly. due to no known magic and how recoil2png/view64 will convert ANYTHING, we disable this for now.
image | [Micrografx Icon](http://fileformats.archiveteam.org/wiki/Micrografx_Icon) | .icn | [4 sample files](https://telparia.com/fileFormatSamples/image/micrografxIcon/) - No known converter.
image | NeoPaint Pattern | .pat | While identified via magic as a "NeoPaint Palette" they appear to be "patterns" used as stamps in the MSDOS Neopaint program. Short of reverse engineering it, in theory dexvert could convert these to images by opening up DOS Neopaint, selecting the pattern, stamping it or filling a canvas with it and saving the image. Don't plan on bothing to actually do that though, it's a relatively obscure program and file format.
image | PC-Draft-CAD Drawing | .dwg | 
image | Telepaint | .ss .st | [7 sample files](https://telparia.com/fileFormatSamples/image/telepaint/)



## Other (217)
Family | Name | Extensions | Notes
------ | ---- | ---------- | -----
other | 3D Construction Kit Area | .3ad | 
other | 3D Construction Kit Object | .3od .obj | 
other | 3D Construction Kit Shape Data | .3sd | 
other | 3D Construction Kit World Data | .kit | 
other | Abuse Level | .lvl .spe | 
other | Adobe Duotone Options | .ado | 
other | Adobe Multiple Master Metrics | .mmm | 
other | Adobe Photoshop Gradient | .grd | 
other | Adobe Type Manager Font Information | .inf | 
other | Alchemy Mindworks Resource | .res | 
other | Alcohol 120% Media Descriptor | .mds | 
other | Allways Printer Driver | .apc .apd .apf | 
other | Alpha Four Script | .scp | 
other | AmiAtlas File | .borders .coasts .index .islands .prefs .rivers .route .town .countries .country | 
other | Amiga Action Replay 3 Freeze File |  | [4 sample files](https://telparia.com/fileFormatSamples/unsupported/amigaActionReplay3/)
other | Amiga ADF BlkDev File | .blkdev | 
other | Amiga ADF Bootcode | .bootcode | 
other | Amiga ADF XDF Meta | .xdfmeta | 
other | Amiga BASIC Protected File | .bas | 
other | Amiga CLI-Mate Directory Index File |  | 
other | Amiga E Module | .m | 
other | Amiga Hunk Library/Object | .lib .obj .o | 
other | Amiga IFF Debug File | .debug | [7 sample files](https://telparia.com/fileFormatSamples/unsupported/iffSDBG/)
other | Amiga IFF DTYP |  | 
other | Amiga Preferences | .prefs | 
other | Amiga Shared Library | .lib | 
other | Amos Amal Animation Bank | .abk | 
other | AMOS ASM Bank | .abk | 
other | AMOS Datas Bank | .abk | [10 sample files](https://telparia.com/fileFormatSamples/unsupported/amosDatasBank/)
other | AMOS Work Bank | .abk | 
other | AniMouse Tutorial | .sdemo | 
other | ArtEffect Brush |  | 
other | ArtEffect Convolution |  | 
other | ASCII Font Metrics | .afm | 
other | Atari CTB File | .ctb | [5 sample files](https://telparia.com/fileFormatSamples/unsupported/atariCTBFile/)
other | Atari GEM OBM File | .obm | [10 sample files](https://telparia.com/fileFormatSamples/other/atariGEMOBM/)
other | Audio Interface Library 3 Digital audio driver | .dig | 
other | Audio Interface Library 3 Music/MIDI driver | .mdi | 
other | AutoCAD Compiled Menu | .mnx | 
other | AutoCAD Protected LISP | .lsp | 
other | Babble! Data | .bab | 
other | Bars and Pipes File | .gchone .gchord .song | 
other | Block Breaker Pattern | .blc | 
other | BNUPORT Patch Table | .pat | 
other | Borland Delphi - C++ Builder Form | .dfm | 
other | Borland Delphi Compiled Unit | .dcu | 
other | Borland Graphics Interface Driver | .bgi | 
other | Borland Language Library | .bll | 
other | Borland Overlay | .ovr | 
other | BOYAN Action Model | .bam | 
other | BWSB Music and Sound Engine Driver | .mse | 
other | CAD/Draw Library | .tbl | 
other | CAD/Draw Settings | .mpi | 
other | CakeWalk Work File | .wrk | 
other | CHAOSultdGEM Parameters | .chs | [8 sample files](https://telparia.com/fileFormatSamples/other/chaosultdGEMParameters/)
other | Chemview Animation Data | .d | 
other | Chess Assistant File | .bic .bid .bim .bis .lib .bfi .dsc .ndx .bdy | 
other | Confusion and Light Compressed Data | .cal | 
other | Corel Editor Macro | .edm | 
other | Corel Shell Macro | .shm | 
other | Corncob 3D Data File | .cct | 
other | Create Adventure Games Project | .cag | 
other | Creative Signal Processor microcode | .csp | 
other | Cybervision Monitor Info |  | 
other | Cygnus Editor Default Settings |  | 
other | Cygnus Editor Macros |  | 
other | dBase Compiled Object Program | .dbo | 
other | dBase Index File | .ntx | 
other | dBase Query | .qbe | 
other | dBase Update | .upd | 
other | DeHackEd Patch | .deh | 
other | Descent Level | .rdl | 
other | DOOM Save Game | .dsg | 
other | Dynamic Message System File | .msg | 
other | Electronic Arts LIB container | .lib | 
other | Emacs Compiled Lisp | .elc | [8 sample files](https://telparia.com/fileFormatSamples/other/emacsCompiledLisp/) - Could decompile it with: https://github.com/rocky/elisp-decompile
other | Ensoniq VFX Patch File | .vfx | 
other | Fiasco Database File | .fdat .fidx .frec .fdb .fpr | 
other | File Express Index Header | .ixh | 
other | File Express Quick Scan | .qss | 
other | Flight Sim Toolkit Terrain Data | .ftd | 
other | FoxPro Memo File | .fpt | 
other | Full Tilt Pinball Data | .dat | 
other | Game Boy ROM | .gb .gbc | 
other | GammaCAD Document | .sym .gc1 | 
other | Gee! Printer Driver | .pdr | 
other | GeoWorks GEOS Data | .000 .001 .002 .003 .004 .005 .006 .007 .008 .009 .010 .011 .012 .geo | 
other | Half-Life 2 Save Game | .sav | 
other | Harvard Graphics Chart | .ch3 | 
other | High Speed Pascal Unit | .unit | 
other | HomeBrew Level | .hle | 
other | HomeBrew Palette | .hpa | 
other | HomeBrew Tile | .hti | 
other | HotMap VBX Regions Description | .hmd | 
other | Human Machine Interfaces Sound Driver | .386 | 
other | HyperPAD Pad | .pad | 
other | ICC Color Map | .iff | 
other | ICC Color Profile | .icc | 
other | IFF Binary Patch | .pch .patch | 
other | Infinity Engine File | .dlg .cre .itm .are .tlk .spl .sto | 
other | InstallShield Uninstall Script | .isu | 
other | Intel Common Object File Format Object | .obj | 
other | Java Class File | .class | [4 sample files](https://telparia.com/fileFormatSamples/other/javaClass/)
other | Javelin Printer Driver | .pr .pr2 | 
other | Jazz Jackrabbit File | .0sc .0fn | 
other | KryoFlux Raw Stream | .raw | [1 sample file](https://telparia.com/fileFormatSamples/unsupported/kryoFluxRawStream/)
other | LabView Virtual Instrument | .vi | 
other | LDIFF Differences Data | .lzd | 
other | Legend of Kyrandia EMC File | .emc | 
other | LIFE 3000 Status | .lif | 
other | LogicSim Circuit |  | 
other | Lotus 1-2-3 Formatting Data | .fm3 | 
other | Lotus 1-2-3 SQZ! Compressed | wq! | 
other | Lotus Magellan Viewer | .vw2 | 
other | LucasFilm Data | .lfd | 
other | Mach-O m68k Object | .o | 
other | MASI Music Driver | .mus | 
other | MathCad Document | .mcd | 
other | MDIFF Patch File | .mdf | 
other | MegaPaint Printer Driver | .trb | 
other | Micro Lathe Object | .lat | 
other | Microsoft Printer Definition | .prd | 
other | Microsoft Program Database | .pdb | 
other | Microsoft Security Catalog | .cat | 
other | Microsoft Separate Debug Format | .dbg | 
other | Microsoft Visual C Files | .bsc .sbr .wsp | 
other | Microsoft Visual C Library | .lib | 
other | Microsoft Windows Program Information File | .pif | 
other | Microsoft Word Style Sheet | .sty | 
other | MIDI Drum Machine | .drm | Program and source at: /browse/111/130%20MIDI%20Tool%20Box.iso/drum
other | MIDI-MAZE II Maze | .mze | 
other | Miles Sound System Driver | .adv | 
other | Moonbase Game Data | .mb | 
other | MS-DOS Code Page Info | .cp .cpi | 
other | NeoPaint Palette | .pal | 
other | NeoPaint Printer Driver | .prd | 
other | Netware Loadable Module | .nlm | 
other | Netware Message | .msg | 
other | Norton Change Directory Info | .ncd | 
other | OLB Library |  | [7 sample files](https://telparia.com/fileFormatSamples/other/olbLib/)
other | Pascal Compiled Unit | .tpu .ppu | 
other | PatchMeister Driver | .pmdriver | 
other | PGP Key Ring | .key .pgp | 
other | Platinen Layout Program Layout | .pla | 
other | Platinen Layout Programm Bibliotheken/library | .bib | 
other | Polyfilm Preferences | .prf | 
other | Ports of Call Save Game | .trp | 
other | Power Up! Album Project | .alb | 
other | PowerBuilder Dynamic Library | .pbd | 
other | Printer Font Metrics | .pfm | 
other | Puzzle Buster Puzzle | .puz | 
other | Quake II Map | .bsp | 
other | Quake II Sprite Reference | .sp2 | 
other | Quake Map | .bsp | 
other | QuickText Titles |  | 
other | Reflections Camera | .kam | 
other | Reflections Data | .r3 | 
other | Reflections Material | .mat | 
other | Reflections Scene |  | 
other | Relocatable Object Module | .obj .o | 
other | RIFF MSFX File | .sfx | Just contains meta info about a given soundeffect usually distributed alongside it as a .wav
other | RIFF MxSt File | .si | References to other files, seems to be meta info only. Only info I could find, failed to process: https://github.com/dutchcoders/extract-riff
other | RIFF Palette | .pal | 
other | RIFF STYL File | .par | References a font for mac and windows and includes some text in a TEXT chunk
other | Rise of the Triad Level | .rtc .rtl | 
other | ROT Object 3D Action | .rotact | 
other | RTPatch File | .rtp | 
other | Scenery Animator Landscape | .scape | 
other | SciTech Driver | .drv | 
other | Scorched Earth Mountain Data | .mtn | 
other | Sculpt 3D Take | .take | 
other | SimCity 2000 Save Game Data | .sc .sc2 | 
other | SimCity City | .cty | 
other | Slicks 'n' Slide Track | .ss | 
other | SmartDraw Template | .sdt .sdr | 
other | SNX Snapshot | .snx | 
other | SoftDisk Library | .shl | 
other | StarCraft Map | .scm .scx | 
other | Startrekker Module Info | .nt | 
other | StarWriter Printer Driver | .gpm | 
other | StarWriter Video Driver | .hgd | 
other | StormWizard Resource | .wizard .wizard-all | 
other | Su-27 Flanker Mission | .mis | 
other | Super ZZT File | .szt | 
other | Superbase Form | .sbv | 
other | SuperJAM! File | .chords .style .section .band .keyboard .patch .drummap | 
other | TADS | .t .gam | 
other | Telix Compiled Script | .slc | 
other | TermInfo |  | 
other | TeX Font Metric Data | .tfm | 
other | TeX Virtual Font | .vf | 
other | TimeZone Data | .tz | 
other | Turbo Lightning Environment | .env | 
other | Turbo Modula-2 Symbol Data | .sym | 
other | Turbo Pascal Help | .hlp | 
other | Type Library | .tlb | 
other | VCD Entries File | .vcd | 
other | Vektor Grafix Driver | .drv | 
other | VESA Display Identification File | .vdb | 
other | VideoTracker Routine | .rot | [10 sample files](https://telparia.com/fileFormatSamples/unsupported/videoTrackerRoutine/)
other | Visual Basic Extension | .vbx | 
other | Visual Basic Tokenized Source | .bas | 
other | Visual FoxPro Compound Index | .cdx | 
other | Visual Smalltalk Enterprise Objects Library | .sll | 
other | Vocal-Eyes Set | .set | 
other | WarCraft Map | .pud | 
other | Windows Help Full Text Search Index | .fts | 
other | Windows Help Global Index Data | .gid | 
other | Windows LOGO Drawing Code | .lgo .lg | 
other | Windows Shortcut | .lnk | 
other | Winzle Puzzle | .wzl | 
other | WordPerfect Driver | .vrs | 
other | WordPerfect for Windows Button Bar | .wwb | 
other | WordPerfect keyboard file | .wpk | 
other | WordPerfect Macro File | .wpm .wcm | 
other | WordPerfect Printer Data | .all .prd | 
other | ZZT File | .zzt | 
