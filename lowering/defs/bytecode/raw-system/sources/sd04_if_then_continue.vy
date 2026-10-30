# selfdestruct in a branch; code after the if must not run when it fires
c: uint256
@external
def foo(t: address, x: uint256) -> uint256:
    if x == 1:
        selfdestruct(t)
    self.c = 5
    return 7
