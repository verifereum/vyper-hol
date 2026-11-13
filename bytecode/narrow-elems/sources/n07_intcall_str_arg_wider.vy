# a narrower String argument staged at the parameter's declared type
@internal
def h(x: String[40], n: uint256) -> uint256:
    return len(x) + n

@external
def d() -> uint256:
    s: String[5] = "hello"
    return self.h(s, 2)
