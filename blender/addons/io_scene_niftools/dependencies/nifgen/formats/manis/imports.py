from importlib import import_module


type_module_name_map = {
	'Byte': 'nifgen.formats.base.basic',
	'Ubyte': 'nifgen.formats.base.basic',
	'Uint64': 'nifgen.formats.base.basic',
	'Int64': 'nifgen.formats.base.basic',
	'Uint': 'nifgen.formats.base.basic',
	'Ushort': 'nifgen.formats.base.basic',
	'Int': 'nifgen.formats.base.basic',
	'Short': 'nifgen.formats.base.basic',
	'Char': 'nifgen.formats.base.basic',
	'Normshort': 'nifgen.formats.base.basic',
	'Rangeshort': 'nifgen.formats.base.basic',
	'Float': 'nifgen.formats.base.basic',
	'Double': 'nifgen.formats.base.basic',
	'Hfloat': 'nifgen.formats.base.basic',
	'ZString': 'nifgen.formats.base.basic',
	'ZStringBuffer': 'nifgen.formats.base.compounds.ZStringBuffer',
	'PadAlign': 'nifgen.formats.base.compounds.PadAlign',
	'FixedString': 'nifgen.formats.base.compounds.FixedString',
	'Vector2': 'nifgen.formats.manis.compounds.Vector2',
	'Vector3': 'nifgen.formats.base.compounds.Vector3',
	'Vector4': 'nifgen.formats.base.compounds.Vector4',
	'Bool': 'nifgen.formats.ovl_base.basic',
	'OffsetString': 'nifgen.formats.ovl_base.basic',
	'Compression': 'nifgen.formats.ovl_base.enums.Compression',
	'VersionInfo': 'nifgen.formats.ovl_base.bitfields.VersionInfo',
	'Pointer': 'nifgen.formats.ovl_base.compounds.Pointer',
	'Reference': 'nifgen.formats.ovl_base.compounds.Reference',
	'LookupPointer': 'nifgen.formats.ovl_base.compounds.LookupPointer',
	'ArrayPointer': 'nifgen.formats.ovl_base.compounds.ArrayPointer',
	'CondPointer': 'nifgen.formats.ovl_base.compounds.CondPointer',
	'ForEachPointer': 'nifgen.formats.ovl_base.compounds.ForEachPointer',
	'MemStruct': 'nifgen.formats.ovl_base.compounds.MemStruct',
	'SmartPadding': 'nifgen.formats.ovl_base.compounds.SmartPadding',
	'ZStringObfuscated': 'nifgen.formats.ovl_base.basic',
	'GenericHeader': 'nifgen.formats.ovl_base.compounds.GenericHeader',
	'Empty': 'nifgen.formats.ovl_base.compounds.Empty',
	'ZStringList': 'nifgen.formats.ovl_base.compounds.ZStringList',
	'ChannelName': 'nifgen.formats.manis.basic',
	'BoneIndex': 'nifgen.formats.manis.basic',
	'Int48': 'nifgen.formats.manis.basic',
	'ManisDtype': 'nifgen.formats.manis.bitfields.ManisDtype',
	'PosBaseKey': 'nifgen.formats.manis.bitfields.PosBaseKey',
	'StoreKeys': 'nifgen.formats.manis.bitfields.StoreKeys',
	'ManisRoot': 'nifgen.formats.manis.compounds.ManisRoot',
	'ManiInfo': 'nifgen.formats.manis.compounds.ManiInfo',
	'Buffer1': 'nifgen.formats.manis.compounds.Buffer1',
	'KeysReader': 'nifgen.formats.manis.compounds.KeysReader',
	'InfoHeader': 'nifgen.formats.manis.compounds.InfoHeader',
	'Vector4H': 'nifgen.formats.manis.compounds.Vector4H',
	'Vector3H': 'nifgen.formats.manis.compounds.Vector3H',
	'FloatsGrabber': 'nifgen.formats.manis.compounds.FloatsGrabber',
	'Segment': 'nifgen.formats.manis.compounds.Segment',
	'String32': 'nifgen.formats.manis.compounds.String32',
	'LocBound': 'nifgen.formats.manis.compounds.LocBound',
	'SegmentsReader': 'nifgen.formats.manis.compounds.SegmentsReader',
	'CompressedManiData': 'nifgen.formats.manis.compounds.CompressedManiData',
	'WarExtraPart': 'nifgen.formats.manis.compounds.WarExtraPart',
	'WarExtra': 'nifgen.formats.manis.compounds.WarExtra',
	'ChunkSizes': 'nifgen.formats.manis.compounds.ChunkSizes',
	'SubChunkReader': 'nifgen.formats.manis.compounds.SubChunkReader',
	'UnkChunkList': 'nifgen.formats.manis.compounds.UnkChunkList',
	'ManiBlock': 'nifgen.formats.manis.compounds.ManiBlock',
	'WeirdElementOne': 'nifgen.formats.manis.compounds.WeirdElementOne',
	'WeirdElementTwoReader': 'nifgen.formats.manis.compounds.WeirdElementTwoReader',
	'SubChunk': 'nifgen.formats.manis.compounds.SubChunk',
	'WeirdElementTwo': 'nifgen.formats.manis.compounds.WeirdElementTwo',
}

name_type_map = {}
for type_name, module in type_module_name_map.items():
	name_type_map[type_name] = getattr(import_module(module), type_name)
for class_object in name_type_map.values():
	if callable(getattr(class_object, 'init_attributes', None)):
		class_object.init_attributes()