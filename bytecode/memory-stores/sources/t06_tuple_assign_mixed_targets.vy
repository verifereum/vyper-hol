# a11: tuple assignment to mixed local/array-elem targets
@internal
def g() -> (uint256, uint256):
    return 1, 2

@external
def f() -> uint256:
    a: uint256 = 0
    arr: uint256[2] = [0, 0]
    a, arr[1] = self.g()
    return a + arr[1]
