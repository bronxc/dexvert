import {Format} from "../../Format.js";

export class superIRG extends Format
{
	name       = "Super IRG/Super IRG 2";
	website    = "http://fileformats.archiveteam.org/wiki/Super_IRG";
	ext        = [".irg", ".ir2"];
	converters = ["recoil2png"];
}
