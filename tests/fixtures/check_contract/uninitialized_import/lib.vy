x: uint256


@internal
@view
def get_x() -> uint256:
    return self.x


@external
def set_x(a: uint256):
    self.x = a


@internal
@pure
def double(a: uint256) -> uint256:
    return 2 * a
