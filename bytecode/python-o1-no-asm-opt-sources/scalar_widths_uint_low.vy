# Integer-width boundary coverage, kept in a two-entry-point module for small evaluation.

@external
def uints_8_64(a: uint8, b: uint16, c: uint24, d: uint32, e: uint40, f: uint48, g: uint56, h: uint64):
    pass

@external
def uints_72_128(a: uint72, b: uint80, c: uint88, d: uint96, e: uint104, f: uint112, g: uint120, h: uint128):
    pass
