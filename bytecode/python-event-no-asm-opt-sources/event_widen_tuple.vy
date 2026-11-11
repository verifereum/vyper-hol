event E:
    a: (uint256, Bytes[5])

@external
def f(x: (uint256, Bytes[3])):
    log E(x)
