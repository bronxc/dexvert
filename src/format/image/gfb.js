import {Format} from "../../Format.js";

export class gfb extends Format
{
	name       = "DeskPic";
	website    = "http://fileformats.archiveteam.org/wiki/DeskPic";
	ext        = [".gfb"];
	magic      = ["DeskPic bitmap"];
	converters = ["recoil2png"];
}
