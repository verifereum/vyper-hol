# internal function name with prefix reachable_
@internal
def reachable_f(y: uint256) -> uint256:
    return y + 1

@external
def foo(x: uint256) -> uint256:
    return self.reachable_f(x)
