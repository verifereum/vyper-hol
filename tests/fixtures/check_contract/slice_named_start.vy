START: constant(uint256) = 3

@external
@view
def f(b: Bytes[2], n: uint256) -> Bytes[2]:
    return slice(b, START, n)
