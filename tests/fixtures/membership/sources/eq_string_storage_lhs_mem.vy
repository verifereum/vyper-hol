# a10: == memory String (lhs) with storage String (rhs)
s: String[40]
@external
def f(a: String[40]) -> bool:
    return a == self.s
