import {Format} from "../../Format.js";

// Fallback match for anything that is just text. This will only be matched as a last resort
export class utf16Text extends Format
{
	name         = "Text (UTF-16)";
	website      = "http://fileformats.archiveteam.org/wiki/Text";
	magic        = ["Unicode text, UTF-16"];	// do NOT include the trid id prefix "Text - UTF-16" as it's too generic
	priority     = this.PRIORITY.LOWEST;
	charSet      = "UTF-16";
	untouched    = true;
	metaProvider = ["text"];
}