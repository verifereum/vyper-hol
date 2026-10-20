
@external
@pure
def decode(payload: Bytes[96]) -> Bytes[32]:
    return abi_decode(payload, Bytes[32])
