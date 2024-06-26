import {Program} from "../../Program.js";
import {Detection} from "../../Detection.js";

export class file extends Program
{
	website = "https://www.darwinsys.com/file/";
	package = "sys-apps/file";
	bin     = "file";
	loc     = "local";
	args    = r => ["--dereference", "--brief", "--keep-going", "--raw", "--", r.inFile()];
	post    = r =>
	{
		const fileMatches = [];
		let fileMatch = null;
		for(let line of r.stdout.trim().replaceAll("\r\n", "\n").split("\n"))
		{
			line = line.replace(/^- /g, "");
			line = line.replace(/^\s*FILE_SIZE=\d+/, "");

			if(!line.length)
				continue;

			if(!fileMatch)
			{
				fileMatch = line;
				continue;
			}

			if(line.startsWith(" ") || [", ", "], ", "), ", "(", "; "].some(v => line.trim().startsWith(v)) || fileMatch.trim().endsWith("[") || line==="]")
			{
				fileMatch += line;
				continue;
			}

			fileMatches.push(fileMatch);
			fileMatch = line;
		}

		fileMatches.push(fileMatch);
		r.meta.detections = fileMatches.map(v => v.trim().replace(/[^ -~]+/g, "")).filter(v => !!v).map((value, i) => Detection.create({value, from : "file", confidence : 100-i, file : r.f.input}));
	};
	renameOut = false;
}
