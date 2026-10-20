# a16 m38d_literal_bound_main: control for m38 with a literal DynArray bound
@external
def f(x: uint256) -> uint256:
    xs: DynArray[uint256, 7] = [x, x]
    return len(xs) + xs[1]
