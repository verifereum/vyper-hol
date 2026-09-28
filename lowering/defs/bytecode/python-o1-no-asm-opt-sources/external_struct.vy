struct Record:
    delta: int128
    enabled: bool
    owner: address
    tag: bytes4

@external
@pure
def record_roundtrip(item: Record) -> Record:
    return item
