# a11: AnnAssign of an empty list literal to a DynArray local (Vyper zero-length fast path)
@external
def f(x: uint256) -> uint256:
    d: DynArray[uint256, 3] = []
    d.append(x)
    return d[0]
