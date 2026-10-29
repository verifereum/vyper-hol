# abi_encode(a, a) assigned to a Bytes[64] memory local (checker acceptance)
@external
@pure
def f(a: uint256) -> Bytes[64]:
    d: Bytes[64] = abi_encode(a, a)
    return d
