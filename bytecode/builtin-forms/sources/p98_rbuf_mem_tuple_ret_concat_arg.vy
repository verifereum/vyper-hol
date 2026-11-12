# return-buffer order: internal returns (Bytes[64], uint256) (memory return), argument is a concat
@internal
def f(b: Bytes[64]) -> (Bytes[64], uint256):
    return b, len(b)

@external
def foo(y: Bytes[32]) -> (Bytes[64], uint256):
    return self.f(concat(y, y))
