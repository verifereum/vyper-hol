# a10: x in memory static array local
@external
def f(x: int128) -> bool:
    a: int128[3] = [x, 2, 3]
    return x in a
