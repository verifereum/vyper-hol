# a11: assign a Bytes argument to a Bytes local after declaration
@external
def f(x: Bytes[40]) -> Bytes[40]:
    b: Bytes[40] = b""
    b = x
    return b
