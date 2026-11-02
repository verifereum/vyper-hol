# extract32 with output_type=address
@external
@pure
def f(b: Bytes[64]) -> address:
    return extract32(b, 4, output_type=address)
