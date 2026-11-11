anchor: uint256
values: uint256[3]

@external
def set_and_get(i: uint256, x: uint256) -> uint256:
    self.values[i] = x
    return self.values[i]
