import {Format} from "../../Format.js";

export class bisWSSPCMAudio extends Format
{
	name           = "BIS WSS PCM Audio";
	ext            = [".wss"];
	forbidExtMatch = true;
	magic          = ["BIS WSS PCM audio", "Bohemia Interactive WSS (wss)"];
	metaProvider   = ["ffprobe[libre]"];
	converters     = ["ffmpeg[libre][format:wss][outType:mp3]"];
}
