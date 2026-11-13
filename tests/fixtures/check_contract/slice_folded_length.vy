N: constant(uint256) = 3

@external
@view
def code_folded() -> Bytes[4]:
    return slice(self.code, 0, N + 1)

@external
@pure
def bytes_folded(b: Bytes[64]) -> Bytes[28]:
    return slice(b, 0, 32 - 4)

@external
@pure
def bytes_runtime(b: Bytes[64], n: uint256) -> Bytes[64]:
    return slice(b, 0, n)
