import {Format} from "../../Format.js";

export class tobiasRichterSlideshow extends Format
{
	name       = "Tobias Richter Fullscreen Slideshow";
	website    = "http://fileformats.archiveteam.org/wiki/Tobias_Richter_Fullscreen_Slideshow";
	ext        = [".pci"];
	mimeType   = "image/x-tobias-richter-fullscreen-slideshow";
	converters = ["recoil2png", `abydosconvert[format:${this.mimeType}]`];
}
