
import flags as library
import bridge as bridge

flag F:
    M0

@external
@pure
def direct_member() -> uint256:
    return convert(library.F.M2, uint256)

@external
@pure
def nested_member() -> uint256:
    return convert(bridge.flags.F.M2, uint256)

@external
@pure
def inverted_member() -> uint256:
    return convert(~library.F.M0, uint256)

@external
@pure
def inverted_argument(item: library.F) -> uint256:
    return convert(~item, uint256)
