import {Format} from "../../Format.js";

export class hci extends Format
{
	name       = "Atari HCI";
	website    = "http://fileformats.archiveteam.org/wiki/HCI";
	ext        = [".hci"];
	fileSize   = 16006;
	converters = ["recoil2png"];
}
