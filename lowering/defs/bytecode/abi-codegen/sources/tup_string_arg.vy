# Tuple with a String member as argument only (calldata decode path).
@external
@pure
def f(x: (uint256, String[10])) -> uint256:
    return 1
