import {xu} from "xu";
import {fileUtil} from "xutil";
import {Program} from "../../Program.js";
import {path} from "std";

export class SID extends Program
{
	website  = "https://github.com/tylerapplebaum/setupinxhacking";
	loc      = "win2k";
	bin      = "c:\\dexvert\\SID\\sid.exe";
	unsafe   = true;
	args     = () => [];
	osData   = r => ({
		script : `
			WinWaitActive("[sid] sexy installshield decompiler", "", 10)

			Sleep(500)
			SendSlow("!fo")

			WinWaitActive("Choose file to decompile", "", 10)
			Sleep(200)
			Send("c:\\in\\${path.basename(r.inFile())}{ENTER}")
			WinWaitClose("Choose file to decompile", "", 10)

			; Dismiss Error dialog
			Local $errorDialog = WinWaitActive("[TITLE:Error]", "", 3)
			If $errorDialog Not = 0 Then
				; Can't click the OK button or close the window any other way than killing it
				KillAll("sid.exe")
			Else
				Local $winHandle = WinGetHandle("[sid] sexy installshield decompiler")

				; Wait for the the progress bar to fill up
				Local $pixelColor
				Local $startTime = GetTime()
				Do
					$pixelColor = PixelGetColor(1015, 729, $winHandle)
					If Hex($pixelColor) == "00000080" Then ExitLoop
					Sleep(50)
				Until TimeDiff($startTime) > ${xu.MINUTE*2}

				Sleep(${xu.SECOND*10})

				ClipPut("")
				Send("^a")
				Sleep(${xu.SECOND*10})
				Send("^c")
				WaitForClipChange(${xu.SECOND*5})
				FileWrite("c:\\out\\out.txt", ClipGet())

				Sleep(500)
				SendSlow("!fq")
				
				WinWaitClose("[sid] sexy installshield decompiler", "", 10)
			EndIf
			
			Sleep(1000)`
	});

	// If our output is exactly 166 bytes and contains the word 'Error' then something went wrong
	verify    = async (r, dexFile) => dexFile.size!==166 || !(await fileUtil.readTextFile(dexFile.absolute)).includes("Error");
	renameOut = true;
}
