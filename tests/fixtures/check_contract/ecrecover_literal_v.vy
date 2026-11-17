# Vyper annotates the literal v as int8.
@external
@pure
def f(h: bytes32, r: uint256, s: uint256) -> address:
    return ecrecover(h, 28, r, s)
