# a11: for over a DynArray of Strings
@external
def f(xs: DynArray[String[10], 3]) -> uint256:
    t: uint256 = 0
    for s: String[10] in xs:
        t += len(s)
    return t
