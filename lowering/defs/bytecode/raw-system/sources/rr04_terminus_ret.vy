# raw_revert as terminus of a function with a return type
@external
def foo(d: Bytes[10]) -> uint256:
    raw_revert(d)
