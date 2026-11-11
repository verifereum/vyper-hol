# a tuple literal with a narrower String element assigned at a wider tuple type
@external
def e(s: String[5]) -> String[40]:
    t: (String[40], uint256) = (s, 1)
    return t[0]
