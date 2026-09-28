@external
@pure
def wei_value(x: uint256) -> uint256:
    return as_wei_value(x, "wei")

@external
@pure
def kwei_value(x: uint256) -> uint256:
    return as_wei_value(x, "kwei")

@external
@pure
def mwei_value(x: uint256) -> uint256:
    return as_wei_value(x, "mwei")

@external
@pure
def gwei_value(x: uint256) -> uint256:
    return as_wei_value(x, "gwei")
