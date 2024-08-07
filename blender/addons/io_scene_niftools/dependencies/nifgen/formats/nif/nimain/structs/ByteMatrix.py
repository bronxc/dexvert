from nifgen.array import Array
from nifgen.base_struct import BaseStruct
from nifgen.formats.nif.imports import name_type_map


class ByteMatrix(BaseStruct):

	"""
	An array of bytes.
	"""

	__name__ = 'ByteMatrix'


	def __init__(self, context, arg=0, template=None, set_default=True):
		super().__init__(context, arg, template, set_default=False)

		# The number of bytes in this array
		self.data_size_1 = name_type_map['Uint'](self.context, 0, None)

		# The number of bytes in this array
		self.data_size_2 = name_type_map['Uint'](self.context, 0, None)

		# The bytes which make up the array
		self.data = Array(self.context, 0, None, (0,), name_type_map['Byte'])
		if set_default:
			self.set_defaults()

	@classmethod
	def _get_attribute_list(cls):
		yield from super()._get_attribute_list()
		yield 'data_size_1', name_type_map['Uint'], (0, None), (False, None), (None, None)
		yield 'data_size_2', name_type_map['Uint'], (0, None), (False, None), (None, None)
		yield 'data', Array, (0, None, (None, None,), name_type_map['Byte']), (False, None), (None, None)

	@classmethod
	def _get_filtered_attribute_list(cls, instance, include_abstract=True):
		yield from super()._get_filtered_attribute_list(instance, include_abstract)
		yield 'data_size_1', name_type_map['Uint'], (0, None), (False, None)
		yield 'data_size_2', name_type_map['Uint'], (0, None), (False, None)
		yield 'data', Array, (0, None, (instance.data_size_2, instance.data_size_1,), name_type_map['Byte']), (False, None)
