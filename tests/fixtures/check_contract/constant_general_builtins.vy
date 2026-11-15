@external
@payable
def wei_default(a: uint256 = msg.value + as_wei_value(1, "ether")) -> uint256:
    return a

@external
@payable
def wei_body() -> uint256:
    return msg.value + as_wei_value(1, "ether")

@external
@pure
def text_default(a: String[78] = uint2str(1)) -> String[78]:
    return a

@external
@pure
def text_body() -> String[78]:
    return uint2str(1)
