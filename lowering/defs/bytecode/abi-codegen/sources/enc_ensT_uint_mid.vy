# abi_encode of a single address, ensure_tuple=True (default), with method_id
@external
@pure
def f(a: address) -> Bytes[36]:
    return abi_encode(a, method_id=0xdeadbeef)
