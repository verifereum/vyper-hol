# @raw_return returning a storage Bytes variable
s: Bytes[40]

@external
@raw_return
def f() -> Bytes[40]:
    return self.s
