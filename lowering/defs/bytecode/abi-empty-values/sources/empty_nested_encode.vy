@external
@pure
def f() -> Bytes[128]:
    return abi_encode(empty(uint256[2][2]), ensure_tuple=False)

