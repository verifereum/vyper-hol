# a struct literal with a narrower String field
struct P:
    s: String[10]
    n: uint256

@external
def c() -> uint256:
    s: String[5] = "hello"
    p: P = P(s=s, n=1)
    return p.n
