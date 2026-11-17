# The result type is the type argument, not the wider return type: an input
# longer than 10 bytes reverts.
@external
@pure
def f(s: Bytes[50]) -> String[100]:
    return convert(s, String[10])

# abi_decode decodes at most 3 elements, whatever the return bound.
@external
@pure
def g(s: Bytes[200]) -> DynArray[uint256, 10]:
    return abi_decode(s, DynArray[uint256, 3])
