import {Format} from "../../Format.js";

export class x11Puzzle extends Format
{
	name       = "X11 Puzzle Image";
	website    = "http://fileformats.archiveteam.org/wiki/Puzzle_image_(X11)";
	ext        = [".cm", ".pzl"];
	converters = ["deark[module:xpuzzle]"];
}