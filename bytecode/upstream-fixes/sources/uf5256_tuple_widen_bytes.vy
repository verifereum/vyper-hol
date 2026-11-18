@external
def f() -> uint256:
    y: (Bytes[2], uint256) = (b"ab", 7)
    x: (Bytes[64], uint256) = y
    return x[1]
