# internal For loop variable (fixed MemLoc in HOL) vs caller local live across the call
x: uint256

@internal
def bar(y: uint256):
    for i: uint256 in range(2):
        self.x += i + y

@external
def foo(x: uint256) -> uint256:
    a: uint256 = x
    self.bar(x)
    return a
