import {Format} from "../../Format.js";

export class hpCOPYDISK extends Format
{
	name           = "HP COPYDISK";
	ext            = [".img", ".dsk"];
	forbidExtMatch = true;
	magic          = ["HP COPYDISK"];
	converters     = ["vibeExtract[singleFile][renameOut]"];
}
