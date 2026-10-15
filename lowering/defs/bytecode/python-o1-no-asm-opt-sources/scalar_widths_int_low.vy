# Integer-width boundary coverage, kept in a two-entry-point module for small evaluation.

@external
def ints_8_64(a: int8, b: int16, c: int24, d: int32, e: int40, f: int48, g: int56, h: int64):
    pass

@external
def ints_72_128(a: int72, b: int80, c: int88, d: int96, e: int104, f: int112, g: int120, h: int128):
    pass
