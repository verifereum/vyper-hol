@external
@pure
def assert_bare(x: uint256) -> uint256:
    assert x != 0
    return x
