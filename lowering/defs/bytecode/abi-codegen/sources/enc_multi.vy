# abi_encode of two scalar args (implicit tuple), no method_id
@external
@pure
def f(a: uint256, b: address) -> Bytes[64]:
    return abi_encode(a, b)
