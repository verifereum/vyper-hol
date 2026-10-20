# a11: append on a local DynArray
@external
def f(x: uint256) -> uint256:
    d: DynArray[uint256, 3] = [1]
    d.append(x)
    return d[1] + len(d)
