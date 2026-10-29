# abi_decode to Bytes[32] with unwrap_tuple=False
@external
@pure
def f(d: Bytes[96]) -> Bytes[32]:
    return abi_decode(d, Bytes[32], unwrap_tuple=False)
