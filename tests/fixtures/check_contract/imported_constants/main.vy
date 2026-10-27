import lib2

K: constant(uint256) = lib2.N + 1

@external
@pure
def k() -> uint256:
    return K
