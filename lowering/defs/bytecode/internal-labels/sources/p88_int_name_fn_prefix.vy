# internal function fn_foo next to external foo (external entry label "fn_" ++ name)
@internal
def fn_foo(y: uint256) -> uint256:
    return y + 1

@external
def foo(x: uint256) -> uint256:
    return self.fn_foo(x)
