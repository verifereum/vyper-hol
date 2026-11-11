# extract32 with output_type=uint256
@external
@pure
def f(b: Bytes[64]) -> uint256:
    return extract32(b, 0, output_type=uint256)
