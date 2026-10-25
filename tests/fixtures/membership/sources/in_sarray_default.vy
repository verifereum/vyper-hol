# a10: 0 in default (empty) static array local -- semantics sparse-array check
@external
def f() -> bool:
    a: uint256[3] = empty(uint256[3])
    return 0 in a
