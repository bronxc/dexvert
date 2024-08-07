import {Format} from "../../Format.js";

export class movieMaker extends Format
{
	name       = "Movie Maker";
	website    = "http://fileformats.archiveteam.org/wiki/Movie_Maker";
	ext        = [".bkg", ".shp"];
	fileSize   = {".bkg" : 3856, ".shp" : [1024, 4384]};
	converters = ["recoil2png"];
}
