# payable external with a default arg
@external
@payable
def f(a: uint256 = 1) -> uint256:
    return a + msg.value
