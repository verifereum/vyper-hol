@external
def f(b: Bytes[10] = empty(Bytes[10])) -> uint256:
    return len(b)
