@external
@pure
def szabo_value(x: uint256) -> uint256:
    return as_wei_value(x, "szabo")

@external
@pure
def finney_value(x: uint256) -> uint256:
    return as_wei_value(x, "finney")

@external
@pure
def ether_value(x: uint256) -> uint256:
    return as_wei_value(x, "ether")

@external
@pure
def kether_value(x: uint256) -> uint256:
    return as_wei_value(x, "kether")
