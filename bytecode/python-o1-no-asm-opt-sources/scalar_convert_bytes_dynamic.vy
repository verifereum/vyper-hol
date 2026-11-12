@external
@pure
def dynbytes_to_bool(x: Bytes[32]) -> bool:
    return convert(x, bool)

@external
@pure
def dynbytes_to_uint(x: Bytes[32]) -> uint256:
    return convert(x, uint256)
