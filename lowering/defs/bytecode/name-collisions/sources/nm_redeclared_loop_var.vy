# a loop variable declared again with another type in a later loop gets its
# own allocation, after the range bound is loaded, as in Python (#644)
@external
def g(n: uint256) -> uint256:
    s: uint256 = 0
    for i: uint256 in range(n, bound=4):
        s += i
    xs: uint8[3] = [1, 2, 3]
    for i: uint8 in xs:
        s += convert(i, uint256)
    return s
