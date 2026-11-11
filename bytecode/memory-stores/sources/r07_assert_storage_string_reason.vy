# a11: assert with a storage String reason
reason: String[20]

@external
def f(x: uint256):
    assert x < 10, self.reason
