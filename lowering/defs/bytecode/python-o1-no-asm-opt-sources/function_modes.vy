stored: uint256

@deploy
def __init__(seed: uint256):
    self.stored = seed

@external
@pure
def pure_pick(flag: bool, a: uint256, b: uint256) -> uint256:
    return a if flag else b

@external
@view
def read_stored() -> uint256:
    return self.stored

@external
@payable
def paid_value() -> uint256:
    return msg.value

@external
def write_stored(v: uint256):
    self.stored = v

@external
@payable
def __default__():
    self.stored = msg.value
