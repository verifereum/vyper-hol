# a memory-passed default: a string literal staged into the callee's buffer
@internal
def f(s: String[10] = "hello") -> uint256:
    return len(s)

@external
def omit() -> uint256:
    return self.f()

@external
def supply(s: String[10]) -> uint256:
    return self.f(s)
