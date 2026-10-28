# Reference: VYPER_PIN cd74ce4f57e3771aeeab8f061fa3be45bfe8a29c
# Compile with experimental_codegen=True, optimize=NONE.
@external
@pure
def multi(a: uint256, b: Bytes[3]) -> Bytes[128]:
    return abi_encode(a, b, ensure_tuple=False)

@external
@pure
def wrapped(a: Bytes[3]) -> Bytes[96]:
    return abi_encode(a, ensure_tuple=True)

@external
@pure
def unwrapped(a: Bytes[3]) -> Bytes[64]:
    return abi_encode(a, ensure_tuple=False)

@external
@pure
def decode_wrapped(a: Bytes[96]) -> Bytes[3]:
    return abi_decode(a, Bytes[3], unwrap_tuple=True)

@external
@pure
def decode_unwrapped(a: Bytes[64]) -> Bytes[3]:
    return abi_decode(a, Bytes[3], unwrap_tuple=False)
