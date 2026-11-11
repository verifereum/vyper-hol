# local named like a storage variable of a different type: each name keeps its
# own location and type (#557, a04-03)
x: DynArray[uint256, 3]

@external
def f() -> uint256:
    self.x.append(7)
    x: uint256 = 5
    return self.x[0] + x + len(self.x)
