@internal
def first(a: DynArray[uint256, 3], b: uint256) -> uint256:
    return len(a)

@external
def f() -> uint256:
    d: DynArray[uint256, 3] = [1, 2]
    return self.first(d, d.pop())
