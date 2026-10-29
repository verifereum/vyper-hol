# abi_decode to DynArray[uint256, 3] with default unwrap_tuple=True
@external
@pure
def f(d: Bytes[192]) -> DynArray[uint256, 3]:
    return abi_decode(d, DynArray[uint256, 3])
