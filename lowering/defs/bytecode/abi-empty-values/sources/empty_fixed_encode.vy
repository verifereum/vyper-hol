@external
@pure
def f() -> Bytes[64]:
    return abi_encode(empty(uint256[2]), ensure_tuple=False)

