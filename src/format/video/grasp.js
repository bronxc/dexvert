import {Format} from "../../Format.js";

export class grasp extends Format
{
	name       = "GRASP Animation";
	website    = "http://fileformats.archiveteam.org/wiki/GRASP_GL";
	ext        = [".gl"];
	magic      = ["GRASP animation", /^deark: graspgl \((Amiga )?GRASP GL\)$/];
	idMeta     = ({macFileType}) => macFileType==="GL  ";
	weakMagic  = true;
	converters = ["vibe2avi"];
}
