@external
@pure
def f(a: uint256) -> Bytes[36]:
    return abi_encode(a, ensure_tuple=False, method_id=method_id("foo()"))
