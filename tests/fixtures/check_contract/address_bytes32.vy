@external
@pure
def to_bytes32(a: address) -> bytes32:
    return convert(a, bytes32)


@external
@pure
def to_bytes21(a: address) -> bytes21:
    return convert(a, bytes21)


@external
@pure
def bytes20_to_bytes32(b: bytes20) -> bytes32:
    return convert(b, bytes32)
