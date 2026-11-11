# extract32 with output_type=int128
@external
@pure
def f(b: Bytes[64]) -> int128:
    return extract32(b, 0, output_type=int128)
