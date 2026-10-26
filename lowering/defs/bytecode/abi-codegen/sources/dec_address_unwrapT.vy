# abi_decode to address with default unwrap_tuple=True
@external
@pure
def f(d: Bytes[32]) -> address:
    return abi_decode(d, address)
