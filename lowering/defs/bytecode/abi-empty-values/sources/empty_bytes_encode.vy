@external
@pure
def f() -> Bytes[64]:
    return abi_encode(empty(Bytes[3]), ensure_tuple=False)

