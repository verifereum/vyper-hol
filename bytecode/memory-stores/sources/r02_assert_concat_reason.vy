# a11: assert with a concat() reason
@external
def f(x: uint256, s: String[10]):
    assert x < 10, concat("bad: ", s)
