import {Format} from "../../Format.js";

export class dreamStation extends Format
{
	name        = "DreamStation Module";
	ext         = [".dss"];
	magic       = ["Dream Station 1.0 module"];
	unsupported = true;
}
