# abi_decode to int8 (clamped) with default unwrap_tuple=True
@external
@pure
def f(d: Bytes[32]) -> int8:
    return abi_decode(d, int8)
