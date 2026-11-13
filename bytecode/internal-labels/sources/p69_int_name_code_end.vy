# internal function named code_end (the codegen data-section label)
@internal
def code_end(y: uint256) -> uint256:
    return y + 1

@external
def foo(x: uint256) -> uint256:
    return self.code_end(x)
