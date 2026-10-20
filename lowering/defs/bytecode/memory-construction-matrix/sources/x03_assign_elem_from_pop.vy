# a11: d[0] = d.pop() on a local DynArray (RHS must be evaluated before target)
@external
def f(a: uint256) -> uint256:
    d: DynArray[uint256, 3] = [a]
    d[0] = d.pop()
    return len(d)
