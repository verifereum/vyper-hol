x: uint256
IMM: immutable(uint256)


@deploy
def __init__(v: uint256):
    IMM = v
    self.x = 1


@internal
def foo() -> uint256:
    return self.x + IMM


@external
def get_x() -> uint256:
    return self.foo()
