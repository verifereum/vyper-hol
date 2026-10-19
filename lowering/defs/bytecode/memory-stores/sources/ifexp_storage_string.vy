# a10: ternary with storage String branch
s: String[20]
@external
def f(c: bool, a: String[20]) -> String[20]:
    return self.s if c else a
