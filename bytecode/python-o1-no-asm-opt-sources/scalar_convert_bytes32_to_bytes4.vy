@external
@pure
def bytes32_to_bytes4(x: bytes32) -> bytes4:
    return convert(x, bytes4)
