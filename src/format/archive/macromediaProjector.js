import {Format} from "../../Format.js";

export class macromediaProjector extends Format
{
	name       = "Macromedia Projector";
	magic      = ["Macromedia Projector"];
	idMeta     = ({macFileType, macFileCreator}) => (macFileType==="APPL" && ["PJ93", "PJ95"].includes(macFileCreator)) || (macFileType==="cdev" && macFileCreator==="FPow");
	converters = ["director_files_extract"];
}
