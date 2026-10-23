@external
@pure
def f(a: String[40]) -> Bytes[132]:
    return abi_encode(a, ensure_tuple=False, method_id=0xdeadbeef)
