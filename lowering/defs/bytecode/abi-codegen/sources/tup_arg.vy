# shallow tuple as external argument
@external
@pure
def f(x: (uint256, bool)) -> uint256:
    return 1
