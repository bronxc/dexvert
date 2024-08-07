import {xu} from "xu";
import {Program} from "../../Program.js";

export class tomsViewer extends Program
{
	website  = "https://tomseditor.com/blog/viewer";
	loc      = "winxp";
	bin      = "c:\\dexvert\\TomsViewer\\TomsViewer.exe";
	args     = r => [r.inFile()];
	osData   = ({
		script : `
			$mainWindow = WindowRequire("Tom's Viewer", "", 7)

			; stream read error shares same title, so we just check for it after requiring the main window, works
			WindowFailure("Tom's Viewer", "Stream Read Error", -1, "{ENTER}")

			; don't be tempted to save as PNG as the program will only work about 25% of the time then, BMP always seems to work
			Send("^s")
			$saveAsWindow = WindowRequire("Save As", "", 5)
			Send("out.bmp{ENTER}")
			WinWaitClose($saveAsWindow, "", 10)

			WaitForStableFileSize("c:\\out\\out.bmp", ${xu.SECOND*3}, ${xu.SECOND*12})

			WinClose($mainWindow, "")`});

	// if the output file is less than 768 bytes we likely failed to convert properly (multiple tiff files fail this way), just delete it
	// NOTE: This was back from when we were doing PNG output, this may not longer be needed for the BMP method
	verify    = (r, dexFile) => dexFile.size>=768;
	classify  = true;
	renameOut = true;
	chain     = "convert";
}
