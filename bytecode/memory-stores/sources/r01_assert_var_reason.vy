# a11: assert with a String local variable as reason
@external
def f(x: uint256):
    reason: String[20] = "too big"
    assert x < 10, reason
