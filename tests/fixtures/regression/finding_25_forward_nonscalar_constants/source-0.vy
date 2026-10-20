
FIRST: constant(Bytes[3]) = SECOND
SECOND: constant(Bytes[3]) = b"abc"
@external
@pure
def value() -> Bytes[3]:
    return FIRST
