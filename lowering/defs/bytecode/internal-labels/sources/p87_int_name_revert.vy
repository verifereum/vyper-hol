# internal function named revert (the codegen revert-stub label)
@internal
def revert(y: uint256) -> uint256:
    return y + 1

@external
def foo(x: uint256) -> uint256:
    return self.revert(x)
