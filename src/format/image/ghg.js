import {Format} from "../../Format.js";

export class ghg extends Format
{
	name       = "Gephard";
	website    = "http://fileformats.archiveteam.org/wiki/Gephard_Hires_Graphics";
	ext        = [".ghg"];
	converters = ["recoil2png"];
}
