# control for nm_local_return_buf: same shape with local named y
@internal
def g() -> uint256:
    y: uint256 = 3
    return y

@external
def f() -> uint256:
    return self.g()
