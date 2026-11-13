# slice of Bytes arg with variable start/len
@external
@pure
def f(a: Bytes[40], s: uint256, l: uint256) -> Bytes[40]:
    return slice(a, s, l)
