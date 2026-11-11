# control: copy of corpus fixture external_struct (prototype regression check)
struct Record:
    delta: int128
    enabled: bool
    owner: address
    tag: bytes4

@external
@pure
def record_roundtrip(item: Record) -> Record:
    return item
