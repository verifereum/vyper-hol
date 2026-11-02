# extract32 with output_type=bytes4 (needs bytesM clamp)
@external
@pure
def f(b: Bytes[64]) -> bytes4:
    return extract32(b, 0, output_type=bytes4)
