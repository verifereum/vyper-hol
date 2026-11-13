N: constant(uint256) = uint256_addmod(1, 2, 7)

@external
@pure
def count() -> uint256:
    s: uint256 = 0
    for i: uint256 in range(N):
        s += 1
    return s
