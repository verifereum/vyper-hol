# extract32 of Bytes arg, default output bytes32
@external
@pure
def f(b: Bytes[64], i: uint256) -> bytes32:
    return extract32(b, i)
