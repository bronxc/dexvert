import {Format} from "../../Format.js";

export class riff extends Format
{
	name       = "RIFF (Generic Fallback)";
	website    = "http://fileformats.archiveteam.org/wiki/RIFF";
	magic      = ["Generic RIFF container", /^RIFF .*data$/];
	fallback   = true;
	converters = ["deark[module:riff]"];
}