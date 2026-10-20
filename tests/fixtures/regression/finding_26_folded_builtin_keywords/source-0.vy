
UNIT: constant(String[5]) = "ether"

@external
@pure
def named(amount: uint256) -> uint256:
    return as_wei_value(amount, UNIT)

@external
@pure
def literal(amount: uint256) -> uint256:
    return as_wei_value(amount, "ether")
