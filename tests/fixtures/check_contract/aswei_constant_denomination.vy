# The denomination is a constant, not a string literal.
DENOM: constant(String[5]) = "ether"

@external
@pure
def f(x: uint256) -> uint256:
    return as_wei_value(x, DENOM)
