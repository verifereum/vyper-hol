struct Pair:
    left: uint256
    right: uint256

anchor: uint256
pair: Pair

@external
def set_and_get(x: uint256) -> uint256:
    self.pair.left = x
    return self.pair.left
