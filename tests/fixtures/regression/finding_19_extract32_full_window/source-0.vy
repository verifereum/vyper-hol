
@external
@pure
def extract_uint(data: Bytes[64], start: uint256) -> uint256:
    return extract32(data, start, output_type=uint256)

@external
@pure
def extract_byte(data: Bytes[64], start: uint256) -> bytes1:
    return extract32(data, start, output_type=bytes1)
