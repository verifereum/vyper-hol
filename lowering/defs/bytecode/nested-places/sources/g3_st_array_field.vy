struct S:
    k: uint256
    arr: uint256[3]

s: S

@external
def f(i: uint256, x: uint256) -> uint256:
    self.s.arr[i] = x
    return self.s.arr[i]
