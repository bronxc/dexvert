import {xu} from "xu";
import {Format} from "../../Format.js";
import {_MOV_MAGIC, _MOV_EXT} from "../video/mov.js";

export class quickTimeAudio extends Format
{
	name             = "Apple QuickTime Audio";
	website          = "http://fileformats.archiveteam.org/wiki/QuickTime";
	ext              = _MOV_EXT;
	magic            = _MOV_MAGIC;
	idMeta           = ({macFileType}) => macFileType==="MooV";
	confidenceAdjust = () => -10;	// Reduce by 10 so that mov matches first
	metaProvider     = ["ffprobe"];
	notes			 = `HUGE room for improvement here. Several files don't convert like "Demo Music File" and "BOMBER_BGM"`;
	converters       = r => ["ffmpeg[outType:mp3]", (r.f.input.size<(xu.MB*25) ? "qt_flatt" : "qtflat")];
}
