struct P:
    x: uint256
    y: uint256

x: uint256

@external
def f(a: uint256) -> uint256:
    m: P = P(x=a, y=2)
    return m.x
