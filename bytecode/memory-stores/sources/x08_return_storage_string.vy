# a11 (lead from a14/a10): return a storage String directly (storage bytestring materialisation)
s: String[20]

@external
def set(v: String[20]):
    self.s = v

@external
def f() -> String[20]:
    return self.s
