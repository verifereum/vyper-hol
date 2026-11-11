@external
@pure
def scalar_roundtrip(
    delta: int128,
    enabled: bool,
    owner: address,
    tag: bytes4,
) -> (int128, bool, address, bytes4):
    return delta, enabled, owner, tag

@external
@pure
def tuple_roundtrip(
    item: (int128, bool, address, bytes4),
) -> (int128, bool, address, bytes4):
    return item
