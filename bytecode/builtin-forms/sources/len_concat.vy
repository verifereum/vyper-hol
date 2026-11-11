# len() of a concat expression (non-located arg)
@external
@pure
def f(a: Bytes[5], b: Bytes[5]) -> uint256:
    return len(concat(a, b))
