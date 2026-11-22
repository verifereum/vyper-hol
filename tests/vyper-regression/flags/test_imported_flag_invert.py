# `~x` has the type of `x`. When `x` is a flag imported from another module,
# the complement ranges over that module's members, even if the current module
# declares a flag of the same name with fewer members.

FLAGS = """
flag F:
    M0
    M1
    M2
"""

CONTRACT = """
import flags as library

flag F:
    M0

@external
@pure
def inverted_member() -> uint256:
    return convert(~library.F.M0, uint256)

@external
@pure
def inverted_argument(item: library.F) -> uint256:
    return convert(~item, uint256)

@external
@pure
def inverted_local_flag() -> uint256:
    return convert(~F.M0, uint256)
"""


def test_imported_flag_invert(get_contract, make_input_bundle):
    bundle = make_input_bundle({"flags.vy": FLAGS})
    c = get_contract(CONTRACT, input_bundle=bundle)

    assert c.inverted_member() == 6
    assert c.inverted_argument(5) == 2
    assert c.inverted_local_flag() == 0
