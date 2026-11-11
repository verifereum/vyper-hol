# c2 with an element whose memory size grows (String[5] into String[40])
@internal
def g(xs: DynArray[String[40], 2]) -> String[40]:
    return xs[1]

@external
def b(s: String[5], t: String[40]) -> String[40]:
    return self.g([s, t])
