# abi_decode to String[32] with default unwrap_tuple=True
@external
@pure
def f(d: Bytes[128]) -> String[32]:
    return abi_decode(d, String[32])
