"""Calls that match no function revert when the contract defines no `__default__`.

Function identifiers: the Solidity ABI specification, "Function Selector". Each test
cites the rule its expectation follows from.
"""

from eth_utils import keccak

CODE = """
@external
def f() -> uint256:
    return 1
"""


def test_matching_identifier_runs_the_function(env, get_contract):
    # docs/control-structures.rst:261 at VYPER_PIN: the default function runs only "if no other
    # functions match the given function identifier", so a matching one runs ``f``. Its return
    # is enc((1,)), one 32-byte word (ABI spec, "Formal Specification of the Encoding").
    c = get_contract(CODE)
    assert env.message_call(c.address, data=keccak(text="f()")[:4]) == (1).to_bytes(32, "big")


def test_unknown_identifier_reverts(env, get_contract, tx_failed):
    # docs/control-structures.rst:281 at VYPER_PIN: "Vyper generates a default function if one
    # isn't found, in the form of a ``REVERT`` call." No function matches ``g()``.
    c = get_contract(CODE)
    with tx_failed():
        env.message_call(c.address, data=keccak(text="g()")[:4])


def test_incomplete_identifier_reverts(env, get_contract, tx_failed):
    # docs/control-structures.rst:261 and :281 at VYPER_PIN: the default function runs "if no
    # other functions match the given function identifier", and the generated one is a
    # ``REVERT``. Three bytes match no function's four-byte identifier (ABI spec, "Function
    # Selector").
    c = get_contract(CODE)
    with tx_failed():
        env.message_call(c.address, data=keccak(text="f()")[:3])
