# internal function with a word-typed local (AnnAssign)
@internal
def bar(y: uint256) -> uint256:
    z: uint256 = y + 1
    return z

@external
def foo(x: uint256) -> uint256:
    return self.bar(x)
