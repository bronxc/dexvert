import {Format} from "../../Format.js";

export class packDir extends Format
{
	name       = "PackDir Archive";
	website    = "http://fileformats.archiveteam.org/wiki/PackDir";
	magic      = ["PackDir archive", "PackDir compressed archive"];
	converters = ["deark[module:packdir]"];
}