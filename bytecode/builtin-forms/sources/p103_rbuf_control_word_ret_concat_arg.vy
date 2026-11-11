# return-buffer order control: internal returns uint256 (no return buffer), argument is a concat
@internal
def f(b: Bytes[64]) -> uint256:
    return len(b)

@external
def foo(y: Bytes[32]) -> uint256:
    return self.f(concat(y, y))
