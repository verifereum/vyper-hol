SIZE: constant(uint256) = 4

@external
@view
def literal(start: uint256) -> Bytes[4]:
    return slice(msg.data, start, 4)

@external
@view
def folded_name(start: uint256) -> Bytes[4]:
    return slice(msg.data, start, SIZE)

@external
@view
def folded_binop(start: uint256) -> Bytes[4]:
    return slice(msg.data, start, 2 + 2)
