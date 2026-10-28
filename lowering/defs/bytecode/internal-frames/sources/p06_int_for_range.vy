# internal function with a range For loop (no AnnAssign)
x: uint256

@internal
def bar():
    for i: uint256 in range(3):
        self.x += i

@external
def foo() -> uint256:
    self.bar()
    return self.x
