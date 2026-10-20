
import bridge as library

@external
@pure
def direct(item: uint256) -> uint256:
    return library.roots.isqrt(item)

@external
@pure
def wrapped(item: uint256) -> uint256:
    return library.wrapped_root(item)
