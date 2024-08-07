import {Format} from "../../Format.js";

export class x3d extends Format
{
	name       = "Extensible 3D";
	website    = "http://fileformats.archiveteam.org/wiki/X3D";
	ext        = [".x3d", ".x3db", ".x3dv", ".x3dz", ".x3dbz", ".x3dvz"];
	magic      = ["X3D (Extensible 3D) model", "Extensible 3D vector graphics", /^fmt\/(579|580)( |$)/];
	converters = ["blender[format:x3d]", "assimp", "polyTrans64[format:x3d]"];
}
