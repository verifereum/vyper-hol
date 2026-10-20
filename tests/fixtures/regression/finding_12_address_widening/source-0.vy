
@external
@pure
def as_bytes21(item: address) -> bytes21:
    return convert(item, bytes21)

@external
@pure
def as_bytes32(item: address) -> bytes32:
    return convert(item, bytes32)

@external
@pure
def widen_bytes(item: bytes20) -> bytes32:
    return convert(item, bytes32)
