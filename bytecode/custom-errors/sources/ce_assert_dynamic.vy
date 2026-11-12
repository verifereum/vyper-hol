error Msg:
    text: String[100]
    n: uint256

@external
def check(x: uint256):
    assert x != 3, Msg("bad value", x)
