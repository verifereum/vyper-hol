# An internal function named like a builtin: the bare call is the builtin.
counter: public(uint256)

@internal
def print(x: uint256):
    self.counter += x

@external
def f():
    a: uint256 = 5
    print(a)
