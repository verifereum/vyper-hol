import lib

SCALE: public(immutable(uint256))


@deploy
def __init__(scale: uint256):
    self.SCALE = scale


@internal
@view
def scaled(a: uint256) -> uint256:
    return lib.double(a) * self.SCALE
