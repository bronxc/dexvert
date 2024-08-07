import {xu} from "xu";
import {programs, init as initPrograms} from "../src/program/programs.js";
await initPrograms();

console.log("Install gentoo with: gentooInstall --phase=2 --scrubPartitionMap --withX --withQEMU --withNode --withSound --gateway=<gateway> <ip> <hostname>");
console.log("Run the following as root on a fresh Gentoo system to be able to run dexvert:\n");

[
	`cd /etc/portage/package.use && ln -s /mnt/compendium/overlay/dexvert/package.use/wine-32 && ln -s /mnt/compendium/overlay/dexvert/package.use/xanim`,
	`cd`,
	`USE="-harfbuzz" emerge -1 media-libs/freetype`,
	`emerge -uDN world`,
	`USE=minimal emerge mono`,
	`USE=minimal emerge -1 libsndfile`,
	`emerge -1 glibc`,	// to pick up on patch
	`emerge --noreplace ${[
		// uniconvertor
		"media-gfx/libimagequant",

		// monitors for changes to files
		"sys-fs/inotify-tools",
		
		// fixes bad filenames
		"app-text/convmv",

		// video meta provider
		"media-video/mplayer",

		// dos
		"games-emulation/dosbox",
		
		// os.js (win2k & winxp)
		"app-emulation/86Box",
		"app-emulation/virtualbox",
		"x11-misc/x11vnc",

		// used by perlTextCheck.js
		"app-arch/trimGarbage",

		// vamos
		"app-arch/amitools",

		// wine
		"app-emulation/wine-vanilla",

		// used by thumbnail creation
		"media-libs/resvg",

		// needed for fontforge, see package.env/fontforge
		"sys-devel/clang",

		// ENSURE that perl is re-compiled with latest system, otherwise perlTextCheck fails on detecting text files properly, such as with: perl -le 'print "Reading: ", -s shift, " bytes\n"; print -B _ ? "Binary File" : "Likely Text (Perl)"' -- test/sample/archive/text/txt/VOTER.DOC
		"dev-lang/perl"
	].join(" ")}`
].forEach(line => console.log(line));

const postPackages =
[
	// these require mono which is 'fully' installed later
	"media-gfx/pablodraw",
	"app-arch/Aaru",

	// dunno why these don't work in the 'big' emerge, but best done after and in a smaller batch
	"games-util/EasyRPG-Tools"
];

const programPackages = Object.values(programs).flatMap(program => Array.force(program.package)).unique().subtractAll(postPackages).sortMulti().join(" ").innerTrim();

[
	`emerge --noreplace ${programPackages}`,
	`emerge mono`,
	`emerge -1 libsndfile`,
	`emerge -uDN world`,
	`# pablodraw usually fails to merge the first time. Just run again: emerge media-gfx/pablodraw`,
	`emerge --noreplace ${postPackages.sortMulti().join(" ")}`,
	`depmod -a`,
	`modinfo vhba`,
	`modprobe vhba`,
	`lsmod`,
	`mkdir /mnt/dexvert`,
	`chown sembiance:sembiance /mnt/dexvert`,
	`usermod -aG vboxusers sembiance`,
	`cd /usr/lib64 && ln -s libimagequant.so libimagequant.so.0`,	// required for uniconvertor
	`echo -e '<?xml version="1.0" encoding="UTF-8"?>\n<oor:data xmlns:oor="http://openoffice.org/2001/registry">\n  <dependency file="main"/>\n  <oor:component-data oor:package="org.openoffice.Office" oor:name="Common">\n    <node oor:name="Misc">\n      <prop oor:name="UseLocking">\n        <value>false</value>\n      </prop>\n    </node>\n  </oor:component-data>\n</oor:data>' > /usr/lib64/libreoffice/share/registry/disable-file-locking.xcd`,
	`find /usr/portage/distfiles/ -mindepth 1 -delete`,
	`emerge --depclean`,
	`revdep-rebuild -pi`,
	`eix-update`,
	`sudo su - sembiance`,
	`echo "Aaru needs to build a database and ask some questions, run it once. Answer 'y' to question #1 about decription and 'n' to all others."`,
	`aaru`,
	`cd ~/bin && ln -s /mnt/compendium/DevLab/dexvert/bin/dextry && ln -s /mnt/compendium/DevLab/dexvert/bin/stopDexserver && ln -s /mnt/compendium/DevLab/dexvert/bin/startDexserver`,
	"# IMPORTANT: Run a full 'dra testMany.js --format=all' to ENSURE that the new dexdrone is functioning properly! DO NOT SKIP THIS STEP"
].forEach(line => console.log(line));
