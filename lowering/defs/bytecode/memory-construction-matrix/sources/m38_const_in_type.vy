# a16 m38_const_in_type: module constant used as a DynArray bound in a local type (folded by the frontend?)
import libp

@external
def f(x: uint256) -> uint256:
    xs: DynArray[uint256, libp.K] = [x, x]
    return len(xs) + xs[1]
