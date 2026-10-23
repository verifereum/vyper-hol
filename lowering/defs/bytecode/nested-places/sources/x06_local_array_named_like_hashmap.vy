m: HashMap[uint256, uint256]

@external
def f(i: uint256, x: uint256) -> uint256:
    m: uint256[2] = [1, 2]
    m[i] = x
    return m[0]
