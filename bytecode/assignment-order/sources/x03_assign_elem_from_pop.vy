@external
def f(a: uint256) -> uint256:
    d: DynArray[uint256, 3] = [a]
    d[0] = d.pop()
    return len(d)
