import {Format} from "../../Format.js";

export class organya extends Format
{
	name        = "Organya Module";
	ext         = [".org"];
	magic       = ["Organya module", "Organya 2 module"];
	unsupported = true;
}
