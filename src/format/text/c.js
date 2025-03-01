import {Format} from "../../Format.js";

export class c extends Format
{
	name           = "C/C++ Source or Header";
	website        = "http://fileformats.archiveteam.org/wiki/C";
	ext            = [".c", ".h", ".cpp", ".cxx", ".cc", ".c++", ".hpp"];
	forbidExtMatch = true;
	filename       = [/source/, /src/];
	weakFilename   = true;
	magic          = [
		// generic
		"C source", "C++ source", "C/C++ Source Code", "C program text", /C source text/, /text C source/,
		
		// specific
		"Qt C-code resource file"
	];
	weakMagic      = true;
	untouched      = true;
	metaProvider   = ["text"];
}
