import {Format} from "../../Format.js";

export class cvg extends Format
{
	name           = "Calamus Vector Graphic";
	website        = "http://fileformats.archiveteam.org/wiki/Calamus_Vector_Graphic";
	ext            = [".cvg"];
	forbidExtMatch = true;	// The magic is pretty robust and without it, scribus takes ages spinning on invalid files
	magic          = ["Calamus Vector Graphic"];
	converters     = ["scribus"];
}
