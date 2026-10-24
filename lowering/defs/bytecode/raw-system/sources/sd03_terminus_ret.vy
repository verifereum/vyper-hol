# selfdestruct as terminus of a function with a return type
@external
def foo(t: address) -> uint256:
    selfdestruct(t)
