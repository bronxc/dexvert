import {Format} from "../../Format.js";

export class spacemaker extends Format
{
	name           = "Spacemaker";
	website        = "http://fileformats.archiveteam.org/wiki/Realia_Spacemaker";
	ext            = [".exe", ".com"];
	forbidExtMatch = true;
	magic          = ["16bit DOS COM Spacemaker compressed", "16bit DOS EXE Spacemaker compressed", "deark: spacemaker"];
	packed         = true;
	converters     = ["deark[module:spacemaker]"];
}
