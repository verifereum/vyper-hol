# abi_encode of a single DynArray arg, default ensure_tuple=True
@external
@pure
def f(a: DynArray[uint256, 3]) -> Bytes[160]:
    return abi_encode(a)
