@external
def foo(b: Bytes[1]) -> address:
    xs: DynArray[uint256, 2] = [1, 2]
    return raw_create(b, xs, xs.pop(), revert_on_failure=False)
