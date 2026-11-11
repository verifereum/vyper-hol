# n02 with an element whose memory size grows (String[5] into String[40])
@internal
def g(xs: DynArray[String[40], 2]) -> String[40]:
    return xs[1]

@external
def b() -> String[40]:
    s: String[5] = "hello"
    t: String[40] = "world"
    return self.g([s, t])
