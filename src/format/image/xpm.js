import {Format} from "../../Format.js";

export class xpm extends Format
{
	name         = "X11 Pixmap";
	website      = "http://fileformats.archiveteam.org/wiki/XPM";
	ext          = [".xpm", ".pm"];
	mimeType     = "image/x-xpixmap";
	magic        = ["X PixMap bitmap", "X-Windows Pixmap Image", "X pixmap image", /^x-fmt\/208( |$)/];
	metaProvider = ["image"];
	converters   = ["convert", "gimp", "canvas", "ffmpeg[outType:png]"];
}
