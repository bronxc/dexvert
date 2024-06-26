export const WEAK_MAC_TYPE_CREATORS =
[
	// these are very generic and can't be acted on
	"BINA/mdos"
];

// These magics are VERY untrustworthy and any detections against them should be noted as such
export const WEAK_VALUES =
[
	// siegfried: WEAK checks
	/^fmt\/(111|134|208|304|347|473|1145|1260|1280|1381|1488|1491|1555|1556|1562|1575|1616|1740|1751|1902)( |$)/,
	/^x-fmt\/(8|10|111|157|195|342)( |$)/,

	// dexmagic: WEAK checks
	/^IFF CAT file$/,
	/^Visual Novel DPK Archive$/,
	/^ZZT World$/,

	// lsar: WEAK checks
	/^LZMA_Alone$/,
	/^Split file$/,

	// pc98ripperID: WEAK checks
	/^PC-98 ElfDOS$/,

	// Detect-It-Easy: WEAK checks
	/^Format: plain text/,
	/^Format: DBase Database \(\.DBF\)/,
	/^Installer: Adveractive/,

	// GT2: WEAK checks
	/^Borland Object Datei/,
	/^DOS Ger.tetreiber/,
	/^Eudora Werbungsdatei$/,
	/^Kopftext/,
	/^JPG Bild/,
	/^Icon Datei/,
	/^IFF Datei/,
	/^INI Datei/,
	/^Lotus 123 Tabelle/,
	/^MAC Bilddatei/,
	/^MPEG \d layer/,
	/^MPEG Filem/,
	/^MPEG-4 Audio Datei/,
	/^PCX Bild/,
	/^Phar Lap \.EXP Datei$/,
	/^POIFS Dokument/,
	/^Unicode Textdatei/,
	/^Windows Maus Cursor Datei\/Works f.r DOS Datei/,
	/^Windows Verkn.*fungs Datei$/,
	/^Wordperfect Dokument Datei/,

	// disktype: WEAK checks
	/^ATARI ST partition map/,
	/^bar archive$/,
	/^Blank disk\/medium$/,
	/^compress-compressed data at /,
	/^FAT\d{2} file system/,
	/^First .* are blank$/,
	/^QNX4 file system$/,
	/^Windows \/ MS-DOS boot loader/,
	
	// FILE: Improper parsing of output
	/^' (123):$/,
	/^$/,	// eslint-disable-line no-control-regex

	// FILE: Very weak checks:
	/^, /,
	/^\(non-conforming\)$/,
	/^0421 Alliant compact executable/,
	/^370 sysV/,
	/^370 XA sysV/,
	/^386 compact demand paged pure executable/,
	/^0420 Alliant virtual executable/,
	/^5View capture file/,
	/^64-bit XCOFF executable or object module/,
	/^68k Blit/,
	/^777 archive data$/,
	/80386 COFF executable/,
	/^Adobe Photoshop Color swatch/,
	/^BALANCE NS32000/,
	/ BCS executable/,
	/^BIOS \(ia32\) ROM Ext/,
	/^ABComp archive data/,
	/^AIX core file/,
	/^ALAN game data/,
	/^Alpha compressed COFF$/,
	/^Alpha u-code object$/,
	/^amd 29k /,
	/^AmigaOS bitmap font/,
	/^Android binary XML/,
	/^Android package resource table/,
	/^Apache Avro/,
	/^Apache Hadoop Sequence/,
	/^Apache Hive RC file/,
	/^Apache ORC/,
	/^Apache Parquet/,
	/^Apollo m68k COFF executable/,
	/^apollo a88k COFF executable/,
	/^Apple DiskCopy 4.2 image/,
	/^Apple QuickTime$/,
	/^Applesoft BASIC program data/,
	/^Arhangel archive data/,
	/^aria2 control file/,
	/^ARM COFF/,
	/^ARMv7 Thumb/,
	/^Atari DEGAS/,
	/^Award BIOS Logo, \d+ x \d+/,
	/^assembler source/,
	/^b\.out/,
	/^basic-16 executable/,
	/^Bio-Rad \.PIC Image File/,
	/^Biosig\/Heka Patchmaster$/,
	/^BOA archive data/,
	/^BS image/,
	/^BSN archive data$/,
	/^CBM BASIC, SYS/,
	/^Clarion Developer/,
	/^CLIPPER COFF executable/,
	/^CMP archive data/,
	/^COFF format/,
	/^Common Data Format \(Version 2\.5 or earlier\) data/,
	/^compacted data$/,
	/^Compiled PSI/,
	/^Convex old-style/,
	/^core file \(Xenix\)$/,
	/^Corel DrawPerfect: Unknown filetype/,
	/^Cytovision FISH Probe file/,
	/^ctab data/,
	/^ddis\/ddif/,
	/^diff output/,
	/^dBase I[IV]I? DBT/,
	/^ddis\/dots archive/,
	/^ddis\/dtif table data/,
	/^DIF \(/,
	/^Disintegrator archive data/,
	/^disk quotas file/,
	/^DitPack archive data$/,
	/DIY-Thermocam raw data/,
	/^DOS .*backed up sequence/,
	/^DOS 2\.0 backup id file/,
	/^Dyalog APL/,
	/^Dzip archive data/,
	/^EBCDIC text/,
	/^EBU-STL subtitles$/,
	/ECOFF executable/,
	/^Encore - version/,
	/^Encore demand-paged executable/,
	/^Encore executable/,
	/^Encore pure executable/,
	/^Encore not stripped/,
	/^Encore unsupported executable/,
	/^ERROR: \(null\)/,
	/^executable \(RISC System\/6000/,
	/^firmware .*revision/,
	/^FIT image data/,
	/^fsav macro virus signatures/,
	/^GDSII Stream file/,
	/^gfxboot compiled html help/,
	/^Generic INItialization configuration/,
	/^GEM NOSIG/,
	/^GeoSwath RDF$/,
	/^Git index, version/,
	/^GLF_BINARY_LSB_FIRST/,
	/^GLF_BINARY_MSB_FIRST/,
	/^GPG encrypted data/,
	/^GTA archive/,
	/^GTA audio index data/,
	/^GTA in-game/,
	/^GTA script/,
	/^GTA1 /,
	/^GTA2 /,
	/^HIT archive data$/,
	/^Hitachi SH/,
	/^HTML document/,
	/^HP 48 binary/,
	/^HPA archive data/,
	/^hp\d00/,
	/^HYP archive data/,
	/^i386 COFF object$/,
	/^iAPX 286 executable/,
	/^ICE authority data$/,
	/^IFF data$/,
	/^IFF data, ASCII text, with no line terminators$/,
	/^Intel ia64 COFF/,
	/^Intel.* Common Object File Format/,
	/^IRIS Showcase file/,
	/^IRIS Showcase template/,
	/jffs2 filesystem data/,
	/^Java.*KeyStore$/,
	/^Java serialization data/,
	/^JPEG-XR$/,
	/^JSON data$/,
	/^JVT NAL sequence/,
	/^Kickstart disk/,
	/^libfprint fingerprint data V\d/,
	/^Linux\/i386 core file/,
	/^Linux LVM1 volume/,
	/^little|big endian ispell/,
	/^locale data table/,
	/^Logitech Compress archive data$/,
	/^lif file/,
	/^LZMA compressed data/,
	/^MacBinary, 2nd header/,
	/^MacBinary.* INVALID date/,
	/^MacBinary, ID [^,]+,/,
	/^MacBinary II,/,
	/^Maple help database$/,
	/^Maple something/,
	/^Matlab v4/,
	/^mc68k COFF/,
	/^mc68k executable/,
	/^Microsoft a\.out/,
	/^Microsoft Visual C\/OMF library$/,
	/^MIPSE[BL][ -]/,
	/^MIT scheme/,
	/^MMDF mailbox/,
	/^Motorola S-Record; binary data in text format$/,
	/^MPEG ADTS, layer I(,|$)/,
	/^MPEG-4 LOAS/,
	/^MS Windows COFF /,
	/^MSX ROM, init/,
	/^MSX-BASIC program/,
	/^MSXiE archive data/,
	/^mumps avl|blt global/,
	/^MySQL table definition file Version 0/,
	/^MySQL table definition file.* type UNKNOWN, MySQL version 0/,
	/^Nim source code/,
	/^Novell LANalyzer capture file/,
	/^NSQ archive data/,
	/^Oak Technologies printer stream/,
	/^old Microsoft 8086 x.out/,
	/^old packed data$/,
	/^old timezone data$/,
	/OpenFirmware FORTH Dictionary/,
	/^OpenPGP Public Key/,
	/^OpenPGP Secret Key/,
	/^OS\/2, hotspot/,
	/^OS9\/68K module$/,
	/^PAK archive data$/,
	/^Palm OS operating system patch data/,
	/^Par archive data$/,
	/^Perkin-Elmer executable/,
	/^PEX Binary Archive$/,
	/^PFT archive data/,
	/^PGP encrypted data/,
	/^PGP key security ring/,
	/^PGP Secret Sub-key/,
	/^PGP symmetric key encrypted data/,
	/^Picasso 64 Image$/,
	/^PDP-11/,
	/Plan 9 executable/,
	/^ps database/,
	/^Psion Series 5 ROM multi-bitmap image$/,
	/^Python script, /,
	/^QDOS object /,
	/^QL OS dump data/,
	/^QL plugin-ROM data/,
	/^QuArk archive data/,
	/^RAD Game Tools Smacker Multimedia/,
	/^RAGE Package Format/,
	/^raw G3/,
	/^RDI Acoustic Doppler Current Profiler/,
	/^RenderWare.* data/,
	/^RIFF \((big|little)-endian\) data$/,
	/^RISC OS outline font data/,
	/^ROOT file/,
	/^SAS$/,
	/^SBX archive data/,
	/^Sega FILM\/CPK Multimedia/,
	/^SHARC COFF binary/,
	/^shared library$/,
	/^shared library TTComp archive data/,
	/^SIMH tape data$/,
	/^Sky archive data/,
	/^SoftQuad DESC or font file binary/,
	/^SoftQuad troff Context intermediate$/,
	/^Sony PlayStation Audio/,
	/^Sony PlayStation PSX image/,
	/^SPARC demand paged/,
	/^Spectrum \.TAP data/,
	/spot sensor temperature/,
	/^SysEx File/,
	/^StarOffice Gallery theme/,
	/^structured file$/,
	/^SVR2 executable/,
	/^SVR2 pure executable/,
	/^SVr\d curses screen image/,
	/^system ID:/,
	/^TeX font metric data/,
	/^TeX generic font data/,
	/^troff or preprocessor input/,
	/^Targa image data/,
	/^Tower\/XP rel/,
	/^Tower32/,
	/^Turbo Pascal TOUR data$/,
	/^Unicode text, UTF-32, big|little-endian$/,
	/^unicos \(cray\) executable/,
	/^unknown demand paged pure executable/,
	/^unknown readable demand paged pure executable/,
	/^VAX-order/,
	/^very short file/,
	/^VISX image file/,
	/^WE32000 COFF/,
	/^Windows boot log/,
	/^Windows Precompiled iNF/,
	/^Windows SYSTEM.INI/,
	/^Windows WIN.INI/,
	/^X1 archive data/,
	/^X11 SNF font data/,
	/^XENIX 8086 relocatable/,
	/^x86 OpenFirmware FORTH Dictionary/,
	/^xBase index/,
	/^xBase, root pointer/,
	/^YAC archive data/,
	/^Zebra Metafile graphic/,

	// TRID: Checks just 1-3 bytes:
	/^1ST Word Plus Document$/,
	/^22DISK format Definition \(tokenized\)$/,
	/^3D-Calc spreadsheet$/,
	/^3M Printscape document \(v1\.x\)$/,
	/^5View capture/,
	/^777 compressed archive$/,
	/^AAX compressed data$/,
	/^ABC notation \(old\)$/,
	/^Adobe PRC 3D model$/,
	/^Advanced DB Master data/,
	/^Affix file$/,
	/^Agfa\/Matrix SCODL bitmap$/,
	/^Alpha Four data \(generic\)$/,
	/^AMI BIOS Energy Star logo bitmap$/,
	/^Amiga bitmap Font/,
	/^Animecha Animation Data$/,
	/^AngelCode Bitmap Font \(binary\)$/,
	/^Any Password data$/,
	/^APE ProSystem Atari 8-bit disk image/,
	/^ArcMac compressed archive$/,
	/^ARHANGEL compressed archive$/,
	/^ArtBorder data$/,
	/^Atari Compressed Disk Communicator image$/,
	/^Atari XE Executable$/,
	/^AutoDesk Revit Indexed Point Cloud$/,
	/^Award BIOS logo bitmap \(\d+x\d+\)/,
	/^AYFX Editor Bank$/,
	/^BALZ compressed data$/,
	/^Band-in-a-Box Song$/,
	/^Bcrypt Encrypted data$/,
	/^Beasts and Bumpkins game data archive$/,
	/^Bennet Yee's face format bitmap$/,
	/Berkeley vfont/,
	/^Big Crunch compressed file$/,
	/^Bio-Rad Image\(s\) bitmap$/,
	/^BIOS ROM Extension \(IA-32\)$/,
	/^Binary NX Vibration data/,
	/^Bit Archiver compressed archive$/,
	/^BitKeeper history data$/,
	/^BSArc compressed archive$/,
	/^BSC ZX Spectrum tape data$/,
	/^BSP bitmap$/,
	/^C64 Hires bitmap$/,
	/^Calcomp raster bitmap$/,
	/^Cardwar Cards deck$/,
	/^CauseWay Compressor compressed data$/,
	/^Chasm CEL bitmap$/,
	/^CheeseCutter Tune$/,
	/^Commodore .*BASIC .*program/,
	/^Compact compressed data/,
	/^Continuous Wave Accelerometry data$/,
	/^Corel Color Palette$/,
	/^Cosmigo Pro Motion SPRites sequence/,
	/^CP\/M 3 COM binary \(no RSX\)$/,
	/^Crosstalk Compiled script$/,
	/^Cubic Tiny XM module$/,
	/^CyberAIDS infected Apple 2 executable$/,
	/^Cybiko Picture bitmap$/,
	/^Dalet Sound format audio (old)$/,
	/^[Dd]ar archive/,
	/^dBASE 5\.0 Multiple index$/,
	/^dBASE IV Multiple index$/,
	/^DEGAS low-res compressed bitmap$/,
	/^DEGAS med-res bitmap$/,
	/^DEGAS med-res compressed bitmap$/,
	/^DEGAS hi-res bitmap$/,
	/^DEGAS hi-res compressed bitmap$/,
	/^DeltaCad drawing$/,
	/^Dialogic VOX \(telephony\) encoded audio$/,
	/^DICOM medical imaging bitmap/,
	/^Digital Micrograph Script$/,
	/^Digital Video$/,
	/^Disk eXPress disk image \(v[012]\.x\)$/,
	/^DiskDupe 5\.12 disk image$/,
	/^DitPack compressed data$/,
	/^Doobs database$/,
	/^Doodle bitmap$/,
	/^Drazpaint \(C64\) bitmap$/,
	/^Dr\. Halo Palette$/,
	/^Dr\. Halo IV Display driver$/,
	/^Dr\. Halo IV Locator driver$/,
	/^Dr\. Halo IV Printer driver$/,
	/^DRM Content Format - Separate delivery file \(generic\)$/,
	/^DURILCA compressed file$/,
	/^Dzip compressed archive$/,
	/^eFax Document \(generic\)$/,
	/^Encrypted Windows App Package \(generic\)$/,
	/^Error Code Modeler$/,
	/^eXtended Triton Format$/,
	/^F64 disk image$/,
	/^Face The Music Effect$/,
	/^FineCrypt encrypted \(v2\.0\)$/,
	/^FinePrint saved output$/,
	/^Flexible Line Interpretation bitmap$/,
	/^Fold\(ed\) compressed archive$/,
	/^F\.R\.A\.C\. project$/,
	/^Freeze! compressed archive$/,
	/^GEM bitmap/,
	/^Generic INI configuration$/,
	/^Genecyst save state$/,
	/^GIF bitmap \(generic\)$/,
	/^Glest 3D model$/,
	/^GLF 3D Font File Format$/,
	/^GNU Info document$/,
	/^GNU Privacy Guard public keyring \(generic\)$/,
	/^GraphiCode Programmable Device Format$/,
	/^Hrust 1 packed/,
	/^interLaced eXtensible Trace/,
	/^Interpaint bitmap$/,
	/^InterWord document$/,
	/^Ipix Spherical Panorama$/,
	/^IPLAY Enterprise Video$/,
	/^ISIS sketch$/,
	/^Janome NH10000 Sewing Machine Stitch$/,	// eslint-disable-line unicorn/better-regex
	/^Java serialized data$/,	// It's just 2 bytes and haven't been able to find a reliable way to convert into something else like JSON
	/^JCALG1 compressed data$/,
	/^JMP data table \(v5\)$/,
	/^Jovian Logic VI bitmap$/,
	/^Jupiter Ace snapshot$/,
	/^Koala Paint/,
	/^Korg SysEx preset command$/,
	/^Legend text$/,
	/^Leonard Guides compiled data$/,
	/^Lepton bitmap/,
	/^Lepton UJG bitmap$/,
	/^LinkWay data$/,
	/^LLVM Bitcode \(generic\)$/,
	/^Lotus Manuscript bitmap$/,
	/^LTAC compressed audio/,
	/^LTP Nuclear ZX tape image$/,
	/^Lucid 3-D Macro$/,
	/^Luxor ABC80 tokenized BASIC source$/,
	/^LZMA compressed archive$/,
	/^LZW compressed data$/,
	/^Mallard BASIC/,
	/^Maple Common Binary file \(generic\)$/,
	/^Master Boot Record dump$/,
	/^Max Payne data file$/,
	/^MegaZeux world data/,
	/^Melco embroidery design$/,
	/^Microsoft Help \(old\)$/,
	/^Microsoft p-code$/,
	/^Microsoft Web query$/,
	/^Mini Office II SpreadSheet$/,
	/^MosASCII Project Workspace$/,
	/^Mozart functor$/,
	/^MP3 audio/,
	/^MSX BASIC tokenized source$/,
	/^MSX ROM Image$/,
	/^MSX2 ROM Image$/,
	/^MultiExpress Data and Fax Cover$/,
	/^MUX video$/,
	/^Mythos Software LIB game data container$/,
	/^NEC JIS encoded file$/,
	/^Nice-Install Data$/,
	/^Nokia Logo Manager bitmap$/,
	/^null bytes$/,
	/^Oberon V4 Symbol data$/,
	/^OCAD map$/,
	/^OMF - Relocatable Object Module Format$/,
	/^Open Access III Data base$/,
	/^OpenStreetMap Binary map data$/,
	/^Organize! Environment$/,
	/^Orao Tape image$/,
	/^OS\/2 Bitmap Graphics Array \(generic\)$/,
	/^Pack compressed data/,
	/^packMP3 compressed MP3 audio$/,
	/^packPNM compressed /,
	/^PaintShow Font$/,
	/^Pajamas Adventure System bitmap$/,
	/^Panasonic JR Cassette image$/,
	/^PAR compressed archive$/,
	/^PAX password protected bitmap$/,
	/^PC9801 rip$/,
	/^PCX bitmap/,
	/^PEA compressed archive/,
	/^Persuasion Presentation \(Mac\)/,
	/^Pervasive Btrieve \(generic\)$/,
	/^Pfaff Compatible design card$/,
	/^PGN \(Portable Gaming Notation\) Compressed format$/,
	/^Philips Respironics M-Series data format$/,
	/^Pixel image$/,
	/^PKCS #7 Signature/,
	/^PlayStation Patch File/,
	/^Pokemon Randomization Quick Settings$/,
	/^Portable Float Map grayscale bitmap$/,
	/^Pretty Good Privacy \(PGP\) Private\/Secret Keyring/,
	/^PrintFox\/Pagefox bitmap/,
	/^ProHance Mouse Keys Definition table/,
	/^Python Pickle serialized data/,
	/^Qmage encoded data$/,
	/^Quarterdeck Mosaic History$/,
	/^raw Group 3 FAX bitmap$/,
	/^Rigol waveform$/,
	/^RPG Maker data$/,
	/^RR compressed data archive$/,
	/^Scamper WARTS storage$/,
	/^SciADV MPK game data Package$/,
	/^Scitex Continuous Tone bitmap$/,
	/^SCODL image$/,
	/^ScreenBuilder image$/,
	/^Shannara video\/animation$/,
	/^Siemens archived SMS messages$/,
	/^Silicon Graphics Object$/,
	/^Siva archive/,
	/^SLZ compressed data$/,
	/^SMS Material$/,
	/^Source Code Control System history data$/,
	/^Sound Club 2 sound bank$/,
	/^Spectrum 512 Anispec animation$/,
	/^Spectrum emulator snapshot$/,
	/^SpeedScript document \(C64\)$/,
	/^Sprint User Interface$/,
	/^SPU Playstation log rip$/,
	/^SQ2 compressed data$/,
	/^Studio Folio Corsage game data archive$/,
	/^Stunt Island Resource$/,
	/^SuperCard Pro flux image$/,
	/^TERSE compressed data \(S?PACK, [UV]\)$/,
	/^Text - UTF-(16|32)/,
	/^TextEngine document \(generic\)$/,
	/^That's Write document$/,
	/^The Apprentice: Los Angeles game data Archive$/,
	/^The Bee Archiver compressed archive$/,
	/^TheC64 Config\/Joystick\/Mode settings$/,
	/^THOR compressed data$/,
	/^Tiny Tafel format$/,
	/^TriloTracker Sample$/,
	/^Trilo Tracker chiptune$/,
	/^TRS-80 Level II BASIC tokenized source$/,
	/^TRSI Sound Monitor song$/,
	/^TTComp archive/,
	/^Turbo Pascal Symbol Table$/,
	/^tzip compressed file$/,
	/^VariCAD Drawing \(generic\)$/,
	/^VersaCAD Shade \(MS-DOS\)$/,
	/^VGAPaint 386 module$/,
	/^Videoscape GEO mesh/,
	/^VisiCalc spreadsheet$/,
	/^WGT Map \(v5\.0\)$/,
	/^WhatsApp encrypted database$/,
	/^White Wolf Productions game data/,
	/^WillDraw Drawing$/,
	/^WinArcadia Saved State$/,
	/^Windows Bitmap$/,
	/^WinPlot data/,
	/^WLF WolfMAME recording info$/,
	/^WordPerfect document \(Amiga\)$/,
	/^X1 compressed archive$/,
	/^XBase DataBase \(generic\)$/,
	/^Xexor disk image$/,
	/^XMash compressed disk image$/,
	/^Yamazaki Zipper compressed archive$/,
	/^Z-Artist Picture bitmap$/,
	/^Z-Code V\d adventure for Infocom Z-Machine$/,
	/^Zoo filter compressed format$/,
	/^Zpng bitmap$/,
	/^ZSNES movie capture$/,
	/^ZX Microdrive cartridge image$/,
	
	// TRID: Checks for almost all zeroes or repeating values/patterns:
	/^3D Studio Shape$/,
	/^A-Robots Fighting Robot Object$/,
	/^Acorn RISC OS font/,
	/^AdLib Timbre Bank Format$/,
	/^Adobe PhotoShop Brush$/,
	/^Aquarius Cassette tape image$/,
	/^Atari NeoChrome bitmap$/,
	/^AudioZip encoded audio$/,
	/^BackupExpress Pro$/,
	/^bCAD Drawing$/,
	/^BS-DOS MB-0\d disk image$/,
	/^Cadwork 2D Catalog$/,
	/^CAJ database$/,
	/^Cat Daddy Games game data archive$/,
	/^ChemDraw model$/,
	/^Chompsters level data$/,
	/^Coordinate 3D \(subset of ADTech File Format\) file \(more generic\)$/,
	/^CP\/M non-bootable disk image$/,
	/^Creative C\/MS packed screen$/,
	/^DOS 2\.0-3\.2 Backup control info/,
	/^Dr\. Halo Font$/,
	/^Dyalog APL transfer$/,
	/^EPOC data store/,
	/^FastCopy DIM disk image$/,
	/^FastDir-like quick directory lookup data$/,
	/^File List Creator list$/,
	/^FleetStreet Installation archive$/,
	/^Generic RIFF container$/,
	/^GnomeVFS$/,
	/^Gravis UltraSound PnP InterWave patch$/,
	/^HandStory eBook$/,
	/^Harvard Graphics Presentation \(v1-3\)$/,
	/^HomeLab\/BraiLab Tape image$/,
	/^HP Logical Interchange Format disk image$/,
	/^HP200LX System Application's Help$/,
	/^Id Software Quake II Cinematic video$/,
	/^IDL binary format save file$/,
	/^Immaginaria TNG 3D scene$/,
	/^Install Maker( Pro)? project$/,
	/^Intel CPU Microcode$/,
	/^Inset PIX bitmap$/,
	/^Kidproof settings \(v1\.0\)$/,
	/^Lotus 123\/Symphony worksheet\/format\/configuration \(V1-V2\)$/,
	/^Luigi's Mansion 3D model$/,
	/^M99 compressed data$/,
	/^MacBinary [12]$/,
	/^MapInfo MapBasic tabular DataBase$/,
	/^Matlab Level 4 MAT-File \(big-endian\)$/,
	/^Microsoft Works for Mac document \(v1\.0\)$/,
	/^Memo File Apollo Database Engine$/,
	/^MICROCAD Drawing$/,
	/^Music Craft Score$/,
	/^MusicMaker Song Data$/,
	/^NIfTI-2 data format/,
	/^Open Minecraft Note Block Studio Song/,
	/^OS\/2 Dynamic Link Library \(no DOS stub\)$/,
	/^PACKER compressed archive$/,
	/^Palantir WinTime Plan$/,
	/^Palm Address Book$/,
	/^Pegasus SPS encoded audio$/,
	/^Photoshop Action$/,
	/^PlayStation Hierarchical 3D Model Data$/,
	/^PlayStation high-speed 3D modeling data$/,
	/^PM XV bitmap/,
	/^Pro Pixel Demo Image$/,
	/^PSX TMD 3d Model$/,
	/^QLAY MDV image$/,
	/^Quarterdeck Installation Package$/,
	/^Quesant AFM data$/,
	/^Sierra AGI music format$/,
	/^Sierra patch$/,
	/^Speccy snapshot$/,
	/^Stunt Island Resource \(generic\)$/,
	/^Sybase iAnywhere database files$/,
	/^Table Apollo \(DBF\) Database Engine$/,
	/^Take Command: 2nd Manassas game data archive$/,
	/^TERSE compressed archive$/,
	/^TeX Font Metric \(0x1[12]\)$/,
	/^Text - UTF-32 \(BE\) encoded$/,
	/^Torque Dynamix Three Space model/,
	/^Turbo Pascal Map/,
	/^UbiArt Framework Cooked Asset$/,
	/^Ulead color Map$/,	// Often matches to this are correct, but it's not a useful file
	/^V-Ray Material \(binary\)$/,
	/^VersaCAD 3D drawing \(MS-DOS\)$/,
	/^Virtual MC-10\/Alice tape image$/,
	/^Visi On Overlay$/,
	/^VXD Driver$/,
	/^VZ200\/300 image \(type F1\)$/,
	/^Warajevo Tape image format$/,
	/^Warcraft game data archive$/,
	/^Windows Device Dependent Bitmap$/,
	/^Windows Jump List$/,
	/^Windows Icon/,
	/^Xerox EDMICS-MMR bitmap$/,
	/^ZealFS disk image$/,

	// TRID: Weak in some other way, such as commonly used word prefix/global/chars string or ascending/descending bytes
	/^4th Dimension database$/,
	/^A-10 Tank Killer game data archive$/,
	/^AceMoney data$/,
	/^Adobe FilmStrip$/,
	/^Amiga Disk image File \(generic\)$/,
	/^Arc System Works game data package$/,
	/^Attack of the PETSCII Robots Amiga module$/,
	/^Audio Disk Jockey bank$/,
	/^BibTeX references$/,
	/^Chasys Draw IES convolution Matrix$/,
	/^Chasys Draw IES Gradient$/,
	/^Chasys Draw IES metadata$/,
	/^Colin McRae Rally 2 game data archive$/,
	/^COM\+ catalog file$/,	// Most matches to this are probably correct, but it's a near worthless file so just ignore it
	/^Cookeo recipe$/,
	/^Dan Bricklin's Demo/,
	/^Dave 2 Huffman compressed game data$/,
	/^Destruction Derby game data$/,	// Actually found matches that were correct, but the id just arters with "PACKED" which is way too weak to match, even with an extension since it just uses .000 and .RAW
	/^Dockerfile$/,
	/^Dynamix Screen data container$/,
	/^EarthSiege 1\/2 game data archive$/,
	/^EA Seattle game data \(UNCS\)$/,
	/^EASE data \(generic\)$/,
	/^EbSynth project$/,
	/^Encrypted Blender 3D data$/,
	/^EVE Online data \(generic\)$/,
	/^Falcon Sequence \(old\)$/,
	/^FCE Ultra FC0 savestate$/,
	/^FGT virus infected 16-bit COM executable$/,
	/^Fine Artist Chunked format/,
	/^Game Boy Advance ROM$/,
	/^Generic IFF container$/,
	/^Gerber format$/,
	/^git index$/,
	/^Grand Theft Auto: San Andreas game data archive$/,
	/^Haines NFF scene/,
	/^Instant Replay Data File$/,
	/^LEGO Mindstorms EV3 brick executable code$/,
	/^Macromedia Director Java Resource - Video$/,
	/^Magic and Mayhem sprites$/,
	/^Mariner Write Document$/,
	/^MegaZeux game$/,
	/^Midtown Madness game data archive$/,
	/^Midtown Madness 2 game data archive$/,
	/^Music Macro Language$/,
	/^Navitel/,
	/^NEOchrome Master bitmap$/,	// Many IFF ILBM files share the same keywords
	/^Novastorm Media audio$/,
	/^OpenSceneGraph native binary format$/,
	/^OpenVPN profile/,
	/^Pacific Warrior 2: Dogfight game data archive$/,
	/^PackDir compressed archive$/,
	/^Poser pose$/,
	/^Psion Organiser Block data$/,
	/^PPrint Image$/,
	/^R3D data stream$/,
	/^Red Baron 3D game data archive$/,
	/^Red Sector Demo-Maker vector/,
	/^Scalable Vector Graphics \(var\.3\)$/,
	/^Scribe Markup$/,
	/^Session Description Protocol \(with rem\)$/,
	/^Beetris high scores$/,	// Other files use the same magic from this publisher
	/^SMS Coastline data$/,
	/^SMS Super File$/,
	/^SMS XYZ data$/,
	/^Snowdrop game data archive$/,
	/^Stunt Island Film$/,
	/^Summation Document Image Information Load File$/,
	/^Super-Card Ami II copier$/,
	/^Sweet Home 3D design \(generic\)$/,
	/^Team Developer \/ SQLWindows application \(binary\)$/,
	/^TeslaCrypt\/Cryptowall encrypted$/,
	/^TOPO topographic Data$/,
	/^Ultimo Primo SnapShot$/,
	/^UNIMod created by APlayer$/,
	/^Vue D'Esprit 4 Atmosphere Preset$/,
	/^WebAssembly module \(binary\)$/,
	/^Wii Model Animation$/,
	/^Xilinx User Constraints File$/,
	/^YSFlight Surface$/,
	/^ZZT Game Creation System/
];
