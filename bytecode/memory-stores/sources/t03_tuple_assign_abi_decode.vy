# a11: tuple assignment from abi_decode
@external
def f(x: Bytes[64]) -> uint256:
    a: uint256 = 0
    b: uint256 = 0
    a, b = abi_decode(x, (uint256, uint256))
    return a + b
