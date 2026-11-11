# a DynArray literal argument with a narrower String element
@internal
def g(xs: DynArray[String[10], 2]) -> uint256:
    return len(xs)

@external
def b() -> uint256:
    s: String[5] = "hello"
    return 1 + self.g([s])
