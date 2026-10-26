# Regression control: a static struct, no tuple staging.
struct S:
    a: uint256
    b: bool

@external
@pure
def f(x: S) -> Bytes[64]:
    return abi_encode(x, ensure_tuple=False)
