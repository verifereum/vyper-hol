# internal with a Bytes local built by concat
@internal
def f(b: Bytes[4]) -> Bytes[8]:
    c: Bytes[8] = concat(b, b)
    return c

@external
def foo(b: Bytes[4]) -> Bytes[8]:
    return self.f(b)
