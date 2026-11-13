# a10: == on storage String with memory String
s: String[40]
@external
def f(a: String[40]) -> bool:
    return self.s == a
