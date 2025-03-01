import {Format} from "../../Format.js";

export class fastgraphPRF extends Format
{
	name        = "Fastgraph Pixel Run Format";
	website     = "http://fileformats.archiveteam.org/wiki/Fastgraph_Pixel_Run_Format";
	ext         = [".prf"];
	magic       = ["Fastgraph Pixel Run Format bitmap"];
	unsupported = true;
	notes       = "No known converter. IMPROCES (see website) can load these images and save as GIF/PCX but sadly it's a mouse driven interface which dexvert can't automate yet.";
}
