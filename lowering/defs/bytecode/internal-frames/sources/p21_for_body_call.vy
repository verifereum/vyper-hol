# internal call inside a For body of an external function
@internal
def f(y: uint256) -> uint256:
    return y + 1

@external
def foo() -> uint256:
    s: uint256 = 0
    for i: uint256 in range(3):
        s = self.f(s)
    return s
