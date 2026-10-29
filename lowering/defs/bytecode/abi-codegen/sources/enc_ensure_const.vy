# abi_encode with ensure_tuple given by a bool constant (False)
E: constant(bool) = False
@external
@pure
def f(a: uint256) -> Bytes[36]:
    return abi_encode(a, ensure_tuple=E, method_id=0xdeadbeef)
