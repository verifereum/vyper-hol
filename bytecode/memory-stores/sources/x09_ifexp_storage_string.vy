# a11 (lead from a14/a10): ternary with a storage String branch, copy of the a10 witness ifexp_storage_string
s: String[20]
@external
def f(c: bool, a: String[20]) -> String[20]:
    return self.s if c else a
