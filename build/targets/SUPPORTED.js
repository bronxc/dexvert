import {xu} from "xu";
import {fileUtil} from "xutil";
import {path} from "std";
import {formats} from "../../src/format/formats.js";
import {DexState} from "../../src/DexState.js";
import {DexFile} from "../../src/DexFile.js";
import {FileSet} from "../../src/FileSet.js";
import {Identification} from "../../src/Identification.js";
import {programs} from "../../src/program/programs.js";

const supportedFormats = Object.fromEntries(Object.entries(formats).filter(([, format]) => !format.unsupported));
const SAMPLES_DIR_PATH = path.join(xu.dirname(import.meta), "..", "..", "test", "sample");

const DUMMY_FILE_PATH = await fileUtil.genTempPath();
await fileUtil.writeFile(DUMMY_FILE_PATH, "x");
const DUMMY_DIR_PATH = await fileUtil.genTempPath();
await Deno.mkdir(DUMMY_DIR_PATH);

export default async function buildSUPPORTED()
{
	xu.log3`Writing SUPPORTED.md to disk...`;
	await fileUtil.writeFile(path.join(xu.dirname(import.meta), "..", "..", "SUPPORTED.md"), `# **${Object.keys(supportedFormats).length.toLocaleString()}** Supported File Formats
Converters are in priority order. That is, earlier entries support the format better than later converters.

Extensions are in order of importance, with the format's primary extension appearing first.

${(await Object.values(supportedFormats).map(f => f.familyid).unique().sortMulti().parallelMap(async familyid => `

## ${familyid.toProperCase()} (${Object.values(supportedFormats).filter(f => f.familyid===familyid).length.toLocaleString()})
Family | Name | Extensions | Converters | Notes
------ | ---- | ---------- | ---------- | -----
${(await Object.values(supportedFormats).filter(f => f.familyid===familyid).sortMulti(f => f.name).parallelMap(async f =>
		{
			const noteParts = [];
			let formatSampleDirPath = path.join(SAMPLES_DIR_PATH, `${f.familyid}/${f.formatid}`);
			if(!await fileUtil.exists(formatSampleDirPath))
				formatSampleDirPath = path.join(SAMPLES_DIR_PATH, `unsupported/${f.formatid}`);
			if(await fileUtil.exists(formatSampleDirPath))
			{
				const formatSamples = await fileUtil.tree(formatSampleDirPath);
				noteParts.push(`[${formatSamples.length.toLocaleString()} sample file${formatSamples.length===1 ? "" : "s"}](https://telparia.com/fileFormatSamples/${path.relative(SAMPLES_DIR_PATH, formatSampleDirPath)}/)`);
			}

			let converters = [];
			if(f.converters)
			{
				if(typeof f.converters==="function")
				{
					const dexState = DexState.create({original : {input : await DexFile.create(DUMMY_FILE_PATH), output : await DexFile.create(DUMMY_DIR_PATH)}});
					dexState.startPhase({format : f, id : Identification.create({from : "dexvert", confidence : 100, magic : f.name}), f : await FileSet.create(path.dirname(DUMMY_FILE_PATH), "input", dexState.original.input)});
					dexState.meta.yes = true;
					
					converters = await f.converters(dexState);
				}
				else
				{
					converters = f.converters;
				}

				converters = converters.map(converter => converter.split("->")[0].trim().split("[")[0].trim());	// get rid of chains
				converters = converters.flatMap(converter => converter.split("&").map(v => v.trim())).unique();	// expand out those that call multiple programs at once and remove duplicates (image/fig (XFig) for example)
				converters = converters.map(programid => (programs[programid] ? `[${programid}](${programs[programid].website})` : programid));
			}
			
			const noteText = (f.notes || "").replaceAll("\n", " ").trim();
			if(noteText && noteText.length>0)
				noteParts.push(noteText);
			return (`${f.familyid} | ${f.website ? `[${f.name}](${f.website})` : f.name} | ${(f.ext || []).join(" ")} | ${(converters || []).join(" ")} | ${noteParts.join(" - ")}`);
		})).join("\n")}
`)).join("\n")}
`);

	xu.log3`Cleaning up...`;
	await fileUtil.unlink(DUMMY_FILE_PATH);
	await fileUtil.unlink(DUMMY_DIR_PATH);
}
