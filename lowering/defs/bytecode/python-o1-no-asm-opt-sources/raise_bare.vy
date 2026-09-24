@external
@pure
def raise_bare(flag: bool) -> uint256:
    if flag:
        raise
    return 1
