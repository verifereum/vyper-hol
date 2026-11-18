# An internal function named like a builtin: the bare call is the builtin.
counter: public(uint256)

@internal
def breakpoint():
    self.counter += 100

@external
def g():
    breakpoint()
