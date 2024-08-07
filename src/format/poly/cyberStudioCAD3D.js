import {Format} from "../../Format.js";

export class cyberStudioCAD3D extends Format
{
	name       = "Cyber Studio/CAD-3D";
	website    = "http://fileformats.archiveteam.org/wiki/CAD-3D";
	ext        = [".3d2", ".3d"];
	magic      = ["Cyber Studio CAD-3D", "CAD-3D object"];
	converters = ["threeDObjectConverter"];
}
