# internal local (fixed MemLoc in HOL) vs caller local live across the call
x: uint256

@internal
def bar(y: uint256):
    z: uint256 = y + 1
    self.x = z

@external
def foo(x: uint256) -> uint256:
    a: uint256 = x
    self.bar(x)
    return a
