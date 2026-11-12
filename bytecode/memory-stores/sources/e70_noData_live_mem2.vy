# zero-field log while a String buffer is live across it
event E:
    pass

@external
def f(s: String[40]) -> String[40]:
    t: String[40] = s
    log E()
    return t
