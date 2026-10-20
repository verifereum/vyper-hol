"""Finding 30: nested imports preserve a builtin module's namespace."""

BRIDGE = """
import math as roots

@internal
@pure
def wrapped_root(item: uint256) -> uint256:
    return roots.isqrt(item)
"""

CONTRACT = """
import bridge as library

@external
@pure
def direct(item: uint256) -> uint256:
    return library.roots.isqrt(item)

@external
@pure
def wrapped(item: uint256) -> uint256:
    return library.wrapped_root(item)
"""


def test_nested_builtin_module_access(get_contract, make_input_bundle):
    bundle = make_input_bundle({"bridge.vy": BRIDGE})
    contract = get_contract(CONTRACT, input_bundle=bundle)
    assert contract.direct(17) == 4
    assert contract.wrapped(17) == 4
