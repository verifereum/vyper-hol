@external
@pure
def encode_static(
    delta: int128,
    enabled: bool,
    owner: address,
    tag: bytes4,
) -> Bytes[132]:
    value: (int128, bool, address, bytes4) = (delta, enabled, owner, tag)
    return abi_encode(value, ensure_tuple=False, method_id=0xdeadbeef)

@external
@pure
def decode_static(data: Bytes[128]) -> (int128, bool, address, bytes4):
    return abi_decode(data, (int128, bool, address, bytes4), unwrap_tuple=False)
