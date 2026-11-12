# n05 with a narrower element but a word return: the DynArray-literal widening alone
@internal
def g(xs: DynArray[String[40], 2]) -> uint256:
    return len(xs)

@external
def b() -> uint256:
    s: String[5] = "hello"
    t: String[40] = "world"
    return self.g([s, t])
