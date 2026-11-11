# SEQ-354 c2: a DynArray literal argument with a narrower String element
@internal
def g(xs: DynArray[String[10], 2]) -> uint256:
    return len(xs)

@external
def b(s: String[5]) -> uint256:
    return 1 + self.g([s])
