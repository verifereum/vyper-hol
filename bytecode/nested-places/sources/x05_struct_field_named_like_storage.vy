struct S:
    a: uint256
    b: uint256

b: uint256

@external
def f(x: uint256) -> uint256:
    st: S = S(a=1, b=x)
    st.b = x + 1
    return st.b
