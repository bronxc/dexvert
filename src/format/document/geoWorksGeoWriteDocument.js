import {Format} from "../../Format.js";

export class geoWorksGeoWriteDocument extends Format
{
	name           = "GeoWorks GeoWrite/Writer document";
	ext            = [".000"];
	forbidExtMatch = true;
	magic          = ["GeoWorks GeoWrite document", "GeoWorks Writer document"];
	converters     = ["vibe2pdf"];
}
