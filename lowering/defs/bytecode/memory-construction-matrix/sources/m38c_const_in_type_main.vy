# a16 m38c_const_in_type_main: control for m38 with a main-module constant as the DynArray bound
K: constant(uint256) = 7

@external
def f(x: uint256) -> uint256:
    xs: DynArray[uint256, K] = [x, x]
    return len(xs) + xs[1]
