# a11 (admitted form): assert reason literal longer than 32 bytes
@external
def f(x: uint256):
    assert x < 10, "this reason string is definitely longer than thirty-two bytes"
