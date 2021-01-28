from __future__ import absolute_import, print_function, unicode_literals

import sys

from wolframclient.utils.api import numpy
from wolframclient.utils.dispatch import Dispatch
from wolframclient.utils.functional import map

encoder = Dispatch()

NUMPY_MAPPING = {
    numpy.int8: "Integer8",
    numpy.int16: "Integer16",
    numpy.int32: "Integer32",
    numpy.int64: "Integer64",
    numpy.uint8: "UnsignedInteger8",
    numpy.uint16: "UnsignedInteger16",
    numpy.uint32: "UnsignedInteger32",
    numpy.uint64: "UnsignedInteger64",
    numpy.float32: "Real32",
    numpy.float64: "Real64",
    numpy.complex64: "ComplexReal32",
    numpy.complex128: "ComplexReal64",
}


SYS_IS_LE = sys.byteorder == "little"


def to_little_endian(array, inplace=False):
    """ Return a numpy array of the same type with little endian byte ordering.

    Set `inplace` to `True` to mutate the input array. """
    endianness = array.dtype.byteorder
    if endianness == ">" or (endianness == "=" and not SYS_IS_LE):
        return array.byteswap(inplace=inplace).newbyteorder()
    else:
        return array


@encoder.dispatch(numpy.ndarray)
def encode_ndarray(serializer, o):

    try:
        wl_type = NUMPY_MAPPING[o.dtype.type]
    except KeyError:
        raise NotImplementedError(
            "NumPy serialization not implemented for %s. Choices are: %s"
            % (repr(o.dtype), ", ".join(map(repr, NUMPY_MAPPING.keys())))
        )

    o = to_little_endian(o)

    if hasattr(o, "tobytes"):
        # Numpy 1.9+ support array.tobytes, but previous versions don't and use tostring instead.
        data = o.tobytes()
    else:
        data = o.tostring()

    return serializer.serialize_numeric_array(data, o.shape, wl_type)


PACKEDARRAY_NUMPY_MAPPING = {
    numpy.int8: ("Integer8", None),
    numpy.int16: ("Integer16", None),
    numpy.int32: ("Integer32", None),
    numpy.int64: ("Integer64", None),
    numpy.uint8: ("Integer16", numpy.int16),
    numpy.uint16: ("Integer32", numpy.int32),
    numpy.uint32: ("Integer64", numpy.int64),
    # numpy.uint64: ("UnsignedInteger64", None),
    numpy.float32: ("Real32", None),
    numpy.float64: ("Real64", None),
    numpy.complex64: ("ComplexReal32", None),
    numpy.complex128: ("ComplexReal64", None),
}
"""
Maps numpy dtype to appropriate wxf packed array type, eventually specifying the type to cast the data to.
"""


@encoder.dispatch(numpy.PackedArray)
def encode_packed_array(serializer, o):
    try:
        wl_type, cast_to = PACKEDARRAY_NUMPY_MAPPING[o.dtype.type]
    except KeyError:
        raise NotImplementedError(
            "Packed array serialization not implemented for %s. Choices are: %s"
            % (repr(o.dtype), ", ".join(map(repr, PACKEDARRAY_NUMPY_MAPPING.keys())))
        )
    o = to_little_endian(o)
    if cast_to is not None:
        o = numpy.array(o, dtype=cast_to)
    if hasattr(o, "tobytes"):
        # Numpy 1.9+ support array.tobytes, but previous versions don't and use tostring instead.
        data = o.tobytes()
    else:
        data = o.tostring()

    return serializer.serialize_packed_array(data, o.shape, wl_type)


@encoder.dispatch(numpy.integer)
def encode_numpy_int(serializer, o):
    return serializer.serialize_int(int(o))


@encoder.dispatch(numpy.floating)
def encode_numpy_floating(serializer, o):
    # mantissa, and base 2 exponent.
    mantissa, exp = numpy.frexp(o)
    return serializer.serialize_function(
        serializer.serialize_symbol(b"Times"),
        (
            serializer.serialize_float(mantissa),
            serializer.serialize_function(
                serializer.serialize_symbol(b"Power"),
                (serializer.serialize_int(2), serializer.serialize_float(exp)),
            ),
        ),
    )


@encoder.dispatch((numpy.float16, numpy.float32, numpy.float64))
def encode_numpy_mp_float(serializer, o):
    return serializer.serialize_float(o)


@encoder.dispatch(numpy.complexfloating)
def encode_complex(serializer, o):
    return serializer.serialize_complex(o)
