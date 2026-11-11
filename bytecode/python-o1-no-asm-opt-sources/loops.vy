@external
@pure
def sum_fixed(xs: uint256[4]) -> uint256:
    total: uint256 = 0
    for x: uint256 in xs:
        total += x
    return total

@external
@pure
def sum_dynamic(n: uint256) -> uint256:
    total: uint256 = 0
    for i: uint256 in range(n, bound=8):
        total += i
    return total
