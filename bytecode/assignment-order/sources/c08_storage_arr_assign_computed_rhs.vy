# a11: evaluate the computed RHS before resolving the storage array target.
arr: uint256[3]

@external
def f(i: uint256, x: uint256):
    self.arr[i] = x + 1
