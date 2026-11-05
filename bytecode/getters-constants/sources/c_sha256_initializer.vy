D: constant(bytes32) = sha256(b"x")

@external
@view
def f() -> bytes32:
    return D
