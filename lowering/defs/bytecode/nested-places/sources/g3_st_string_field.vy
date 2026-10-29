struct S:
    k: uint256
    name: String[10]

s: S

@external
def f(x: String[10]) -> String[10]:
    self.s.name = x
    return self.s.name
