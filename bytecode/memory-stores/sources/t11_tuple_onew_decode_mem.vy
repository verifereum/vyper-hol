@external
def f(data: Bytes[64], x: uint256[1]) -> uint256:
    a: uint256 = 0
    c: uint256[1] = x
    a, c = abi_decode(data, (uint256, uint256[1]))
    return a + c[0]
