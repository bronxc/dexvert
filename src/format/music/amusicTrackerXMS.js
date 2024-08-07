import {Format} from "../../Format.js";

export class amusicTrackerXMS extends Format
{
	name         = "AMUSIC Adlib Tracker XMS";
	website      = "http://fileformats.archiveteam.org/wiki/XMS-Tracker_module";
	ext          = [".xms"];
	magic        = ["XMS Adlib Module Composer", "XMS-Tracker module", "XMS Adlib Module"];
	metaProvider = ["musicInfo"];
	converters   = ["adplay"];
}
