from nifgen.base_enum import BaseEnum
from nifgen.formats.nif.basic import Uint


class BSShaderCRC32(BaseEnum):

	__name__ = 'BSShaderCRC32'
	_storage = Uint

	CAST_SHADOWS = 1563274220
	ZBUFFER_TEST = 1740048692
	ZBUFFER_WRITE = 3166356979
	TWO_SIDED = 759557230
	VERTEXCOLORS = 348504749
	PBR = 731263983
	SKINNED = 3744563888
	ENVMAP = 2893749418
	VERTEX_ALPHA = 2333069810
	FACE = 314919375
	GRAYSCALE_TO_PALETTE_COLOR = 442246519
	DECAL = 3849131744
	DYNAMIC_DECAL = 1576614759
	HAIRTINT = 1264105798
	SKIN_TINT = 1483897208
	EMIT_ENABLED = 2262553490
	GLOWMAP = 2399422528
	REFRACTION = 1957349758
	REFRACTION_FALLOFF = 902349195
	NOFADE = 2994043788
	INVERTED_FADE_PATTERN = 3030867718
	RGB_FALLOFF = 3448946507
	EXTERNAL_EMITTANCE = 2150459555
	MODELSPACENORMALS = 2548465567
	TRANSFORM_CHANGED = 3196772338
	EFFECT_LIGHTING = 3473438218
	FALLOFF = 3980660124
	SOFT_EFFECT = 3503164976
	GRAYSCALE_TO_PALETTE_ALPHA = 2901038324
	WEAPON_BLOOD = 2078326675
	LOD_OBJECTS = 2896726515
	NO_EXPOSURE = 3707406987