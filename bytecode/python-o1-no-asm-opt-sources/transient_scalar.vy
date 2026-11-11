anchor: uint256
scratch: transient(uint256)

@external
def set_add_read(x: uint256) -> uint256:
    self.scratch = x
    self.scratch += 1
    return self.scratch
