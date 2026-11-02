#pragma enable-decimals

N: constant(uint256) = 3


@external
@pure
def pow_literal_base(y: uint8) -> uint8:
    return 3 ** y


@external
@pure
def pow_literal_exponent(x: int8) -> int8:
    return x ** 3


@external
@pure
def pow_negative_literal_base(y: int256) -> int256:
    return (-2) ** y


@external
@pure
def pow_constant_exponent(x: uint256) -> uint256:
    return x ** N


@external
@pure
def pow_augmented(x: uint256) -> uint256:
    z: uint256 = x
    z **= 2
    return z


@external
@pure
def neg_signed(x: int8) -> int8:
    return -x


@external
@pure
def neg_decimal(x: decimal) -> decimal:
    return -x


@external
@pure
def shl_literal_amount(x: uint256) -> uint256:
    return x << 4


@external
@pure
def shr_signed_value(x: int256, y: uint8) -> int256:
    return x >> y


@external
@pure
def shift_augmented(x: uint256, y: uint256) -> uint256:
    z: uint256 = x
    z <<= y
    z >>= 4
    return z
