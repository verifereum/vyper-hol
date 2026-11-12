# n01 with an element whose memory size grows (String[5] into String[40])
@internal
def f(t: (String[40], uint256)) -> uint256:
    return t[1]

@external
def a() -> uint256:
    s: String[5] = "hello"
    return 1 + self.f((s, 1))
