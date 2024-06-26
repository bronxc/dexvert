import {Format} from "../../Format.js";

export class cmf extends Format
{
	name         = "Creative Music Format";
	website      = "http://fileformats.archiveteam.org/wiki/Creative_Music_Format";
	ext          = [".cmf"];
	magic        = ["Creative Music Format", "Creative Music (CMF) data"];
	notes        = "If I encounter formats that don't convert, try falling back to sandbox/app/cmf2mid.exe";
	metaProvider = ["musicInfo"];
	converters   = ["adplay", "gamemus[format:cmf-creativelabs]"];
}
