# abi_encode of a single Bytes arg, default ensure_tuple=True
@external
@pure
def f(a: Bytes[40]) -> Bytes[160]:
    return abi_encode(a)
