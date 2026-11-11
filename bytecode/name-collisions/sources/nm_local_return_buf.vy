# local named __return_buf__ inside an internal function
@internal
def g() -> uint256:
    __return_buf__: uint256 = 3
    return __return_buf__

@external
def f() -> uint256:
    return self.g()
