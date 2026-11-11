# a11: memory target st.arr[i] = x (array field of local struct)
struct S:
    arr: uint256[2]
    b: uint256

@external
def f(i: uint256, x: uint256) -> uint256:
    st: S = S(arr=[1, 2], b=3)
    st.arr[i] = x
    return st.arr[1]
