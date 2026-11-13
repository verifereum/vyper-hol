# a10: x not in memory static array argument (uint8)
@external
def f(x: uint8, a: uint8[4]) -> bool:
    return x not in a
