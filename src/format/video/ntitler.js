import {Format} from "../../Format.js";

export class ntitler extends Format
{
	name        = "NTitler Animation";
	ext         = [".nt"];
	magic       = ["NTitler show"];
	unsupported = true;
	notes       = "Couldn't locate a converter or extractor. Original Amiga program is here: http://aminet.net/package/gfx/misc/ntpro";
}
