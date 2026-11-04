# dynamic array of structs whose fields need no clamp (uint256, bytes32) as argument
struct S:
    a: uint256
    b: bytes32

@external
@pure
def f(x: DynArray[S, 2]) -> uint256:
    return len(x)
