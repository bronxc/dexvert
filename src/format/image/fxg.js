import {Format} from "../../Format.js";

export class fxg extends Format
{
	name       = "Flash XML Graphics";
	website    = "http://fileformats.archiveteam.org/wiki/FXG";
	ext        = [".fxg"];
	magic      = ["Flash XML Graphics"];
	mimeType   = "image/x-flash-xml-graphics";
	converters = [`abydosconvert[format:${this.mimeType}]`];
}
