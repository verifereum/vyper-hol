# abi_encode of a single Bytes arg, ensure_tuple=False
@external
@pure
def f(a: Bytes[40]) -> Bytes[128]:
    return abi_encode(a, ensure_tuple=False)
