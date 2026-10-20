
counter: int256

@internal
def bump() -> int256:
    self.counter += 1
    return self.counter

@external
def comparison() -> bool:
    self.counter = 0
    return self.bump() < self.bump()

@external
def unsafe_subtraction() -> int256:
    self.counter = 0
    return unsafe_sub(self.bump(), self.bump())

@external
def unsafe_division() -> int256:
    self.counter = 0
    return unsafe_div(self.bump(), self.bump())

@external
def modular_power() -> uint256:
    self.counter = 0
    return pow_mod256(convert(self.bump(), uint256), convert(self.bump(), uint256))
