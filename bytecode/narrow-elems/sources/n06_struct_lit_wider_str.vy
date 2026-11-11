# c3 with a field whose memory size grows (String[5] into String[40])
struct P:
    s: String[40]
    n: uint256

@external
def c(s: String[5]) -> (String[40], uint256):
    p: P = P(s=s, n=7)
    return p.s, p.n
