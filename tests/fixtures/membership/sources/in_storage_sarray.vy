# a10: x in storage static array
s: uint8[2]
@external
def f(x: uint8) -> bool:
    return x in self.s
