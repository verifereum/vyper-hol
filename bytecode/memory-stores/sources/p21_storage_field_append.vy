struct S:
    prefix: uint256
    items: DynArray[uint256, 4]

s: S

@external
def f(v: uint256) -> DynArray[uint256, 4]:
    self.s.items.append(v)
    return self.s.items
