import {Program} from "../../Program.js";

export class vcd_info extends Program
{
	website = "https://www.gnu.org/software/vcdimager";
	package = "media-video/vcdimager";
	bin     = "vcd-info";
	args    = r => [`--bin-file=${r.inFile()}`];
	post    = r =>
	{
		let curHeader = undefined;
		r.stdout.trim().split("\n").filter(v => !!v).forEach((line, i) =>
		{
			if((/^VCD [\d.]+ detected$/).test(line.trim()))
				r.meta.isVCD = true;
			
			if(curHeader===null)
			{
				curHeader = line.trim();
				return;
			}

			if((/^-+$/).test(line))
			{
				if(i>0)
					curHeader = null;
				return;
			}

			const props = (line.trimEnd().match(/^\s+(?<name>[^:]+):\s+(?<val>.+)$/) || {})?.groups;
			if(!curHeader?.endsWith("primary volume descriptor") || !props)
				return;
			
			let propName = {"ID" : "id", "ISO size" : "isoSize"}[props.name] || props.name.toCamelCase().replaceAll(" ", "").trim();
			if(propName.endsWith("Id"))
				propName = `${propName.slice(0, -2)}ID`;
			r.meta[propName] = props.val.trimChars(["`", "'"]);
		});
	};
	renameOut = false;
}
