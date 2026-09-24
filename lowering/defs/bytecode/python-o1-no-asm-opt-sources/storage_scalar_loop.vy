counter: uint256

@external
def set_add_in_loop(x: uint256) -> uint256:
    self.counter = x
    for i: uint256 in range(3):
        self.counter += i
    return self.counter
