# len() of a Bytes calldata argument
@external
@pure
def f(b: Bytes[40]) -> uint256:
    return len(b)
