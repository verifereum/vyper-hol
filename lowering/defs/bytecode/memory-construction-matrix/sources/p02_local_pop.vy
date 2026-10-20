# a11: pop on a local DynArray (statement and expression)
@external
def f() -> uint256:
    d: DynArray[uint256, 3] = [1, 2, 3]
    d.pop()
    return d.pop()
