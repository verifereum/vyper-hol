# return-buffer order: internal returns (uint256, uint256) (two stack returns, scratch alloca), argument is a concat
@internal
def f(b: Bytes[64]) -> (uint256, uint256):
    return len(b), 7

@external
def foo(y: Bytes[32]) -> (uint256, uint256):
    return self.f(concat(y, y))
