import {Format} from "../../Format.js";

export class truePaint extends Format
{
	name       = "True Paint I";
	website    = "http://fileformats.archiveteam.org/wiki/True_Paint_I";
	ext        = [".mci", ".mcp"];
	fileSize   = {".mci" : 19434};
	byteCheck  = [{ext : ".mcp", offset : 0, match : [0x01, 0x08]}];
	converters = ["view64", "recoil2png[format:MCI]"];
}
