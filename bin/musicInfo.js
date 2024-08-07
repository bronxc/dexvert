/* eslint-disable @stylistic/brace-style */
import {xu, fg} from "xu";
import {runUtil, cmdUtil, fileUtil, printUtil} from "xutil";
import {path} from "std";

const argv = cmdUtil.cmdInit({
	version : "1.0.0",
	desc    : "Returns meta info about music file at <inputFilePath>",
	opts    :
	{
		debug      : {desc : "Output debug info"},
		jsonOutput : {desc : "Output results as JSON instead of being human readable"}
	},
	args :
	[
		{argid : "inputFilePath", desc : "File path to identify", required : true}
	]});

const musicWAVFilePath = path.join(path.dirname(argv.inputFilePath), "music.wav");
const noMusicWAV = await fileUtil.exists(musicWAVFilePath);
const tmpDirPath = await fileUtil.genTempPath(undefined, "musicInfo");
await Deno.mkdir(tmpDirPath);

const runOptions = {timeout : xu.SECOND*5};

const {stderr : xmpInfoRaw} = await runUtil.run("xmp", ["-Cv", "-o", "/dev/null", argv.inputFilePath], runOptions);
const {stdout : uadeInfoRaw} = await runUtil.run("uade123", ["-g", argv.inputFilePath], runOptions);
const {stdout : openMPTInfoRaw} = await runUtil.run("openmpt123", ["--info", argv.inputFilePath], runOptions);
const {stdout : mikmodInfoRaw} = await runUtil.run("mikmodInfo", [argv.inputFilePath], runOptions);
const {stdout : timidityInfoRaw} = await runUtil.run("timidity", ["-Ow", "-o", "/dev/null", argv.inputFilePath], runOptions);
const {stdout : zxtuneRaw} = await runUtil.run("zxtune123", ["--file", argv.inputFilePath, "--null", "--quiet"], {stdoutUnbuffer : true, ...runOptions});
const {stderr : adplayRaw} = await runUtil.run("adplay", ["--once", "--instruments", "-O", "disk", "-d", "/dev/null", argv.inputFilePath], runOptions);
await runUtil.run("asapconv", ["-o", path.join(tmpDirPath, "%n:_:%a.wav"), argv.inputFilePath], runOptions);

if(argv.debug)
	[["xmpInfoRaw", xmpInfoRaw], ["uadeInfoRaw", uadeInfoRaw], ["openMPTInfoRaw", openMPTInfoRaw], ["mikmodInfoRaw", mikmodInfoRaw], ["timidityInfoRaw", timidityInfoRaw], ["zxtuneRaw", zxtuneRaw], ["adplayRaw", adplayRaw]].forEach(([k, v]) => console.log(`${fg.yellow(k)}\n${v}`));

const musicInfo = {};

const infos = {};
try { infos.xmp = parseXMP(xmpInfoRaw); } catch {}
try { infos.uade = parseUADE(uadeInfoRaw); } catch {}
try { infos.openMPT = parseOpenMPT(openMPTInfoRaw); } catch {}
try { infos.mikmod = parseMikmod(mikmodInfoRaw); } catch {}
try { infos.timidity = parseTimidity(timidityInfoRaw); } catch {}
try { infos.zxtune = parseZXTune(zxtuneRaw); } catch {}
try { infos.adplay = parseAdplay(adplayRaw); } catch {}
try { infos.asap = await parseASAP(); } catch {}

if(argv.debug)
	console.log(infos);

// Earlier program entries produce better meta data and are processed in priority order
for(const type of ["xmp", "uade", "openMPT", "mikmod", "timidity", "zxtune", "adplay", "asap"])
{
	const subInfo = infos[type];

	// Trim certain properties
	for(const propName of ["title", "type", "tracker", "author"])
	{
		if(subInfo?.[propName])
		{
			if(subInfo[propName].trim().length>0)
				subInfo[propName] = subInfo[propName].trim();
			else
				delete subInfo[propName];
		}
	}

	// now assign our properties to musicInfo
	["title", "type", "tracker", "patternCount", "sampleCount", "trackCount", "instruments", "author"].forEach(propName =>
	{
		if(Object.hasOwn(musicInfo, propName))
			return;

		if(subInfo?.[propName])
			musicInfo[propName] = subInfo[propName];
	});
}

// These two programs produce the best title (UTF8 characters properly rendered, see s3m/FISTROPI.S3M) So override title if we have these
for(const type of ["zxtune", "openMPT"])	// in reverse priority since it clobbers previous
{
	const subInfo = infos[type];
	if(subInfo.title)
		musicInfo.title = subInfo.title;
}

if(!noMusicWAV)
	await fileUtil.unlink(musicWAVFilePath);
await fileUtil.unlink(tmpDirPath, {recursive : true});

if(argv.jsonOutput)
	console.log(JSON.stringify(musicInfo));
else
	console.log(printUtil.columnizeObject(musicInfo));

function parseXMP(infoRaw="")
{
	const lines = (infoRaw || "").trim().split("\n");
	if(lines.length===0)
		return;
	
	const info = {instruments : []};
	let instrumentSection = false;
	let instrumentNameEndLoc = null;

	lines.forEach(line =>
	{
		if(line.startsWith("Instruments:"))
		{
			instrumentSection = true;
			return;
		}

		if(instrumentSection)
		{
			if(instrumentNameEndLoc===null)
				instrumentNameEndLoc = line.match(/(?<precursor>\s+Instrument name\s+).*/).groups.precursor.length;
			else
				info.instruments.push(line.substring(3, instrumentNameEndLoc).trimEnd());
		}
		else
		{
			for(const [propKey, propInfo] of Object.entries({
				title        : {re : /^Module name[^:]+:\s(?<value>.+)$/},
				tracker      : {re : /^Module type[^:]+:\s(?<value>.+)$/},
				patternCount : {re : /^Patterns[^:]+:\s(?<value>\d+)$/, num : true},
				sampleCount  : {re : /^Samples[^:]+:\s(?<value>\d+)$/, num : true},
				trackCount   : {re : /^Channels[^:]+:\s(?<value>\d+).*$/, num : true}}))
			{
				const matchProps = line.match(propInfo.re);
				if(!matchProps)
					continue;
				
				info[propKey] = propInfo.num ? +matchProps.groups.value : matchProps.groups.value;
			}
		}
	});

	info.instruments = info.instruments.filter(v => !!v);
	if(info.instruments.length===0)
		delete info.instruments;

	return info;
}

function parseUADE(infoRaw="")
{
	const lines = (infoRaw || "").trim().split("\n");
	if(lines.length===0)
		return;
	
	const info = {};
	lines.forEach(line =>
	{
		for(const [propKey, propInfo] of Object.entries({
			title : {re : /^modulename:\s(?<value>.+)$/},
			type  : {re : /^playername:\s(?<value>.+)$/}}))
		{
			const matchProps = line.match(propInfo.re);
			if(!matchProps)
				continue;
			
			info[propKey] = propInfo.num ? +matchProps.groups.value : matchProps.groups.value;
		}
	});

	return info;
}

function parseOpenMPT(infoRaw="")
{
	const lines = (infoRaw || "").trim().split("\n");
	if(lines.length===0)
		return;
	
	let instrumentSection = false;

	const info = {instruments : []};
	lines.forEach(line =>
	{
		if(line.startsWith("instruments:"))
		{
			instrumentSection = true;
			return;
		}

		if(instrumentSection)
		{
			info.instruments.push(line);
			return;
		}

		for(const [propKey, propInfo] of Object.entries({
			title        : {re : /^Title\.*:\s(?<value>.+)$/},
			type         : {re : /^Type\.*:\s(?<value>.+)$/},
			tracker      : {re : /^Tracker\.*:\s(?<value>.+)$/},
			trackCount   : {re : /^Channels\.*:\s(?<value>.+)$/, num : true},
			patternCount : {re : /^Patterns\.*:\s(?<value>.+)$/, num : true},
			sampleCount  : {re : /^Samples\.*:\s(?<value>.+)$/, num : true}}))
		{
			const matchProps = line.match(propInfo.re);
			if(!matchProps)
				continue;
			
			info[propKey] = propInfo.num ? +matchProps.groups.value : matchProps.groups.value;
		}
	});

	if(info.instruments.length===0)
		delete info.instruments;

	return info;
}

function parseMikmod(infoRaw="")
{
	const lines = (infoRaw || "").trim().split("\n");
	if(lines.length===0)
		return;

	let instrumentSection = false;

	const info = {instruments : []};
	lines.forEach(line =>
	{
		if(line.startsWith("instruments:"))
		{
			instrumentSection = true;
			return;
		}

		if(instrumentSection)
		{
			if(line.trim().length>0 && line.trim()!=="(null)")
				info.instruments.push(line);
			return;
		}

		for(const [propKey, propInfo] of Object.entries({
			title        : {re : /^name:(?<value>.+)$/},
			tracker      : {re : /^type:(?<value>.+)$/},
			trackCount   : {re : /^channels:(?<value>.+)$/, num : true},
			patternCount : {re : /^patterns:(?<value>.+)$/, num : true},
			sampleCount  : {re : /^samples:(?<value>.+)$/, num : true}}))
		{
			const matchProps = line.match(propInfo.re);
			if(!matchProps)
				continue;
			
			info[propKey] = propInfo.num ? +matchProps.groups.value : matchProps.groups.value;
		}
	});

	if(info.instruments.length===0)
		delete info.instruments;

	return info;
}

function parseTimidity(infoRaw="")
{
	const lines = (infoRaw || "").trim().split("\n");
	if(lines.length===0)
		return;
	
	const info = {};
	lines.forEach(line =>
	{
		for(const [propKey, propInfo] of Object.entries({
			title : {re : /^\((?<value>[^)]+)\).*$/}}))
		{
			const matchProps = line.match(propInfo.re);
			if(!matchProps)
				continue;
			
			info[propKey] = propInfo.num ? +matchProps.groups.value : matchProps.groups.value;
		}
	});

	return info;
}

function parseZXTune(infoRaw="")
{
	const lines = (infoRaw || "").trim().replaceAll("\t", "\n").split("\n");
	if(lines.length===0)
		return;

	const info = {};
	lines.forEach(line =>
	{
		for(const [propKey, propInfo] of Object.entries({
			title   : {re : /^Title:(?<value>.+)$/},
			type    : {re : /^Type:(?<value>.+)$/},
			tracker : {re : /^Program:(?<value>.+)$/},
			author  : {re : /^Author:(?<value>.+)$/}}))
		{
			const matchProps = line.match(propInfo.re);
			if(!matchProps)
				continue;
			
			// zxtunes can have multiple sub tracks, combine em together
			const value = matchProps.groups.value.trim();
			if(value.length)
			{
				info[propKey] ||= [];
				info[propKey].pushUnique(value);
			}
		}
	});

	for(const key of Object.keys(info))
	{
		if(info[key]?.length>0)
			info[key] = info[key].join(" ");
		else
			delete info[key];
	}

	return info;
}

function parseAdplay(infoRaw="")
{
	const lines = (infoRaw || "").trim().split("\n");
	if(lines.length===0)
		return;

	let instrumentSection = false;

	const info = {instruments : []};
	lines.forEach(line =>
	{
		if(line.startsWith("Instrument names:"))
		{
			instrumentSection = true;
			return;
		}

		if(instrumentSection)
		{
			if(line.length>4)
			{
				const instrument = line.substring(4).trimEnd();
				if(instrument!=="unnamed" && instrument.trim().length>0)
					info.instruments.push(instrument);
			}
			return;
		}

		for(const [propKey, propInfo] of Object.entries({
			title   : {re : /^Title\s*:(?<value>.+)$/},
			type    : {re : /^Type\s*:(?<value>.+)$/},
			author  : {re : /^Author\s*:(?<value>.+)$/}}))
		{
			const matchProps = line.match(propInfo.re);
			if(!matchProps)
				continue;
			
			info[propKey] = matchProps.groups.value.trim();
			if(info[propKey].length===0)
				delete info[propKey];
		}
	});

	if(info.instruments.length===0)
		delete info.instruments;

	return info;
}

async function parseASAP()
{
	const outputFilePaths = await fileUtil.tree(tmpDirPath, {nodir : true, depth : 1, relative : true, regex : /\.wav$/});
	if(outputFilePaths.length===0)
		return;
	
	const [title, author] = path.basename(outputFilePaths[0], ".wav").split(":_:");
	if(title===path.basename(argv.inputFilePath, path.extname(argv.inputFilePath)) && !author?.length)
		return;

	return {title, author};
}
