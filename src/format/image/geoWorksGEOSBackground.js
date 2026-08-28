import {Format} from "../../Format.js";

export class geoWorksGEOSBackground extends Format
{
	name           = "GeoWorks GEOS background";
	ext            = [".000", ".geo"];
	forbidExtMatch = true;
	magic          = ["GeoWorks GEOS background"];
	converters     = ["vibe2png"];
}
