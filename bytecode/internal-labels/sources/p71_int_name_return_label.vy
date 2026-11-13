# internal function name with prefix return_label_
@internal
def return_label_f(y: uint256) -> uint256:
    return y + 1

@external
def foo(x: uint256) -> uint256:
    return self.return_label_f(x)
