import {Format} from "../../Format.js";

export class paperPortMAX extends Format
{
	name           = "PaperPort Scanned Image";
	website        = "http://fileformats.archiveteam.org/wiki/PaperPort_(MAX)";
	ext            = [".max"];
	forbidExtMatch = true;
	magic          = ["PaperPort scanned document/image", "Visioneer PaperPort", "Archive: PaperPort", /^fmt\/(1223|1224|1225|1339)( |$)/];
	converters     = ["paperPort"];
}
