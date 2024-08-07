import {Program} from "../../Program.js";

export class leaftoppm extends Program
{
	website    = "http://netpbm.sourceforge.net/";
	package    = "media-libs/netpbm";
	bin        = "leaftoppm";
	args       = r => [r.inFile()];
	runOptions = async r => ({stdoutFilePath : await r.outFile("out.ppm")});
	renameOut  = true;
	chain      = "convert";
}
