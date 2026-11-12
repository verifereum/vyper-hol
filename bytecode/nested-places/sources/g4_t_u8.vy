x: transient(uint8)

@external
def f(a: uint8) -> uint8:
    self.x = a
    return self.x
