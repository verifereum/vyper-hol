# internal fn_foo (called from bar) next to external foo, which does not call it
@internal
def fn_foo(y: uint256) -> uint256:
    return y + 1

@external
def foo(x: uint256) -> uint256:
    return x * 3

@external
def bar(x: uint256) -> uint256:
    return self.fn_foo(x)
