# A call through a nested module alias path (`library.roots.isqrt`) runs the
# function in the module that path names, here the builtin `math` module that
# `bridge` imports, exactly as a call through a wrapper in `bridge` does.

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


def test_nested_module_call(get_contract, make_input_bundle):
    bundle = make_input_bundle({"bridge.vy": BRIDGE})
    c = get_contract(CONTRACT, input_bundle=bundle)

    assert c.direct(17) == 4
    assert c.wrapped(17) == 4
