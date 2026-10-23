# `UNREACHABLE` as an assert's message and as a raise's exception.
@external
@pure
def guarded(x: uint256) -> uint256:
    assert x < 10, UNREACHABLE
    return x


@external
@pure
def nonzero(x: uint256) -> uint256:
    if x == 0:
        raise UNREACHABLE
    return x
