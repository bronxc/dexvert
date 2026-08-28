import {Format} from "../../Format.js";

export class mohawkWAVE extends Format
{
	name           = "Mohawk WAVE File";
	ext            = [".sndl", ".seq", ".pal", ".shpl", ".cnt", ".bmp", "._scr", ".scrb", ".mfo", ".puzz", ".shap", ".shp#", ".unit", ".fscn", ".cur", ".snd", ".mid", "view"];
	forbidExtMatch = true;
	magic          = ["Mohawk WAVE File", "Broderbund's Mohawk (mhwk)"];
	converters     = ["vibe2wav[renameOut]", "ffmpeg[libre][format:mhwk][outType:mp3]"];
}
