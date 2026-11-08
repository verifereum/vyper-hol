import lib

M: constant(uint256) = N + 1
N: constant(uint256) = 2

@external
@pure
def total(values: uint256[M], more: uint256[lib.W]) -> uint256:
    s: uint256 = 0
    for i: uint256 in range(M):
        s += values[i]
    return s + more[0]
