import {Format} from "../../Format.js";

export class frameMaker extends Format
{
	name           = "FrameMaker";
	website        = "http://fileformats.archiveteam.org/wiki/FrameMaker";
	ext            = [".fm", ".frm", "doc"];
	forbidExtMatch = true;
	magic          = ["FrameMaker document"];
	converters     = ["frameMaker"];
}