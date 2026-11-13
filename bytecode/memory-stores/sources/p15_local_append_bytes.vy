@external
def f(b: Bytes[10]) -> uint256:
    d: DynArray[Bytes[10], 3] = []
    d.append(b)
    return len(d[0])
