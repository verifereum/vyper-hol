S: constant(String[5]) = "abc"

@external
def f() -> uint256:
    return len(S)
