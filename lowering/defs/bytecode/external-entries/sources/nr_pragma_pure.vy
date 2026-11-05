# nonreentrancy-by-default pragma with a pure external function (vyper: pure never locks)
#pragma nonreentrancy on

@external
@pure
def f(a: uint256) -> uint256:
    return a + 1
