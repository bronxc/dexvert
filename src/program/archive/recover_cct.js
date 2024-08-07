import {xu} from "xu";
import {Program} from "../../Program.js";
import {path} from "std";

export class recover_cct extends Program
{
	website  = "https://archive.org/details/recover_cct";
	unsafe   = true;
	loc      = "winxp";
	bin      = "c:\\dexvert\\recover-cct\\recover-cct.exe";
	args     = () => [];
	osData   = r => ({
		dontMaximize : true,
		script       : `
			WindowRequire("Where is ", "", 10)
			Sleep(200)
			Send("c:\\in\\${path.basename(r.inFile())}{ENTER}")
			
			; Wait for the first Where is to go away
			Sleep(1000)
		
			; Wait for the second one to appear then dismiss it
			WinWaitActive("Where is ", "", 10)
			Sleep(200)
			Send("{ESCAPE}")

			; Wait for main window to appear
			WinWaitActive("recover-cct", "", 10)

			; Wait 10 seconds for file to be written
			$unprotectedFilePath = "c:\\dexvert\\recover-cct\\unprotected_.cst"
			WaitForStableFileSize($unprotectedFilePath, ${xu.SECOND*3}, ${xu.MINUTE})

			; Now kill the program
			KillAll("recover-cct.exe")

			; Now move the resulting file out of the recover-cct dir and into our out dir
			FileMove($unprotectedFilePath, "c:\\out\\dexvert.cst")`
	});

	// We rename the file dexvert to ensure we don't collide with an existing filename, seems to fix some problems with 'find by.Dir' sample
	renameOut = {name : "dexvert"};
}
