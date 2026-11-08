@external
def f() -> uint256:
    d: DynArray[uint256, 3] = [5]
    d[0] += d.pop()
    d.append(7)
    return d[0]
