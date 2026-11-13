@external
@view
def code_runtime(n: uint256) -> Bytes[4]:
    m: uint256 = n
    return slice(self.code, 0, 4)
