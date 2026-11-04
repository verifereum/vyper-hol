# return-buffer order, plain case: internal returns Bytes[64] (memory return), word argument only
@internal
def f(x: uint256) -> Bytes[64]:
    return concat(convert(x, bytes32), convert(x + 1, bytes32))

@external
def foo(x: uint256) -> Bytes[64]:
    return self.f(x)
