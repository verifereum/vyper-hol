a: uint256[1]

@external
def f() -> uint256:
    x: uint256[1] = self.a
    return x[0]
