d: transient(DynArray[uint256, 3])

@external
def f(x: uint256) -> uint256:
    self.d.append(x)
    return self.d.pop()
