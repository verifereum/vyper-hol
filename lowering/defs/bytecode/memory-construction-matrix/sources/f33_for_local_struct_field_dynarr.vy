# a11: iterate over a local struct's DynArray field st.d
struct S:
    n: uint256
    d: DynArray[uint256, 3]

@external
def f(a: uint256) -> uint256:
    st: S = S(n=1, d=[a, 2])
    t: uint256 = 0
    for x: uint256 in st.d:
        t += x
    return t
