# a11 control (supported): assert with a literal string reason
@external
def f(x: uint256):
    assert x < 10, "too big"
