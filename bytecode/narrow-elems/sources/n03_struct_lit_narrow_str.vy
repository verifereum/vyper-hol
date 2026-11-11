# SEQ-354 c3: a struct literal with a narrower String field
struct P:
    s: String[10]
    n: uint256

@external
def c(s: String[5]) -> uint256:
    p: P = P(s=s, n=1)
    return p.n
