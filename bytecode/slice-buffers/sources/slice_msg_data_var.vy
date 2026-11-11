# slice of msg.data with variable start
@external
@view
def f(s: uint256) -> Bytes[8]:
    return slice(msg.data, s, 8)
