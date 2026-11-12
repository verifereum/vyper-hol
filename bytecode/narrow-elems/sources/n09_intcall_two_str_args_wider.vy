# two narrower String arguments: the second staging buffer follows the first
# at the first parameter's declared size
@internal
def h(x: String[40], y: String[40]) -> uint256:
    return len(x) + len(y)

@external
def d() -> uint256:
    s: String[5] = "hello"
    t: String[5] = "world"
    return self.h(s, t)
