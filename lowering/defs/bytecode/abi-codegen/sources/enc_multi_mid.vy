# abi_encode of two scalar args with method_id (ensure_tuple irrelevant)
@external
@pure
def f(a: uint256, b: address) -> Bytes[68]:
    return abi_encode(a, b, ensure_tuple=False, method_id=0xdeadbeef)
