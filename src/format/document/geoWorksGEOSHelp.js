import {Format} from "../../Format.js";

export class geoWorksGEOSHelp extends Format
{
	name           = "GeoWorks GEOS help";
	ext            = [".000"];
	forbidExtMatch = true;
	magic          = ["GeoWorks GEOS help"];
	converters     = ["vibe2pdf"];
}
