@external
@pure
def unsafe_add_u8(a: uint8, b: uint8) -> uint8:
    return unsafe_add(a, b)

@external
@pure
def unsafe_sub_u8(a: uint8, b: uint8) -> uint8:
    return unsafe_sub(a, b)

@external
@pure
def unsafe_mul_u8(a: uint8, b: uint8) -> uint8:
    return unsafe_mul(a, b)

@external
@pure
def unsafe_div_u8(a: uint8, b: uint8) -> uint8:
    return unsafe_div(a, b)
