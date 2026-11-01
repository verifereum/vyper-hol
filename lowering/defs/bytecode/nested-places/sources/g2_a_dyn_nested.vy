d: DynArray[DynArray[uint256, 3], 3]

@external
def f(x: uint256) -> uint256:
    self.d.append([x])
    self.d[0].append(x)
    return self.d[0][1]
