# abi_decode to Bytes[32] with default unwrap_tuple=True (dynamic: tuple-wrapped encoding)
@external
@pure
def f(d: Bytes[128]) -> Bytes[32]:
    return abi_decode(d, Bytes[32])
