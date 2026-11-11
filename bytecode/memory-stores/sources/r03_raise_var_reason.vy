# a11: raise with a String local reason
@external
def f(x: uint256):
    reason: String[20] = "nope"
    if x > 3:
        raise reason
