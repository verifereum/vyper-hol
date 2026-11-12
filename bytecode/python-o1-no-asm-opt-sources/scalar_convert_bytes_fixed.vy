@external
@pure
def bytes32_to_uint(x: bytes32) -> uint256:
    return convert(x, uint256)
