import {Format} from "../../Format.js";

export class mtvMovie extends Format
{
	name         = "MTV Movie";
	website      = "http://fileformats.archiveteam.org/wiki/MTV_Movie_(.MTV)";
	ext          = [".mtv"];
	magic        = ["MTV Multimedia File", "MTV video", "MTV (mtv)"];
	metaProvider = ["mplayer"];
	converters   = ["ffmpeg[format:mtv]"];
}
