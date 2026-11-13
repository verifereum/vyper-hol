struct S:
    n: uint256
    arr: uint256[3]

st: S

@external
def f() -> uint256:
    t: uint256 = 0
    for x: uint256 in self.st.arr:
        t += x
    return t
