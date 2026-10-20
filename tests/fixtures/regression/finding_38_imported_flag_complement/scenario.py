"""Finding 38: imported flag complement uses the imported flag's width."""

FLAGS = """
flag F:
    M0
    M1
    M2
"""

BRIDGE = """
import flags as flags
"""

CONTRACT = """
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
"""


def test_complement_keeps_imported_flag_identity(get_contract, make_input_bundle):
    bundle = make_input_bundle({"flags.vy": FLAGS, "bridge.vy": BRIDGE})
    contract = get_contract(CONTRACT, input_bundle=bundle)

    assert contract.direct_member() == 4
    assert contract.nested_member() == 4
    assert contract.inverted_member() == 6
    assert contract.inverted_argument(5) == 2
