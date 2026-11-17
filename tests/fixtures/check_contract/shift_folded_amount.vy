# Vyper folds the shift amount, which it annotates int8.
@external
@pure
def f(x: uint256) -> uint256:
    return x << (2 + 1)
