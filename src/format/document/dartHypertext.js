import {Format} from "../../Format.js";

export class dartHypertext extends Format
{
	name        = "Dart Hypertext";
	magic       = ["Dart hypertext"];
	unsupported = true;
	notes       = "The DART/DART.EXE program in sandbox/apps/ can open these, it's a text format. It has no way to export as text. It can 'print' the file, but the dosbox I'm using doesn't support printing. Thus this format isn't currently supported.";
}
