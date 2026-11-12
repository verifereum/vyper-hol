# a tuple literal with a narrower String element assigned at a wider tuple type
@external
def e() -> String[40]:
    s: String[5] = "hello"
    t: (String[40], uint256) = (s, 1)
    return t[0]
