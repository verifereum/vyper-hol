M: constant(bytes4) = 0xdeadbeef
@external
@pure
def f(a: uint256) -> Bytes[36]:
    return abi_encode(a, ensure_tuple=False, method_id=M)
