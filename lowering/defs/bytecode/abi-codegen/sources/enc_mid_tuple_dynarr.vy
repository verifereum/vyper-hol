# abi_encode of tuple (uint256, DynArray) with method_id, ensure_tuple=False
@external
@pure
def f(a: uint256, d: DynArray[uint256, 2]) -> Bytes[164]:
    v: (uint256, DynArray[uint256, 2]) = (a, d)
    return abi_encode(v, ensure_tuple=False, method_id=0xdeadbeef)
