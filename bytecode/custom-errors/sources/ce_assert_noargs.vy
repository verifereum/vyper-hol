error Simple:
    pass

@external
def check(x: uint256):
    assert x > 0, Simple()
