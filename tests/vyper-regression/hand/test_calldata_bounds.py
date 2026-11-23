"""Calldata arguments longer than their declared bound revert, with calldata written by hand.

Calldata layout: the Solidity ABI specification, "Function Selector and Argument
Encoding" and "Formal Specification of the Encoding". Each test cites the rule for
its revert.
"""

from eth_utils import keccak


def word(n: int) -> bytes:
    return n.to_bytes(32, "big")


def selector(signature: str) -> bytes:
    return keccak(text=signature)[:4]


def test_bytes_argument_over_bound_reverts(env, get_contract, tx_failed):
    # docs/interfaces.rst:162 at VYPER_PIN: "If the value the caller passes is longer than the
    # implementation's declared bound, the callee reverts when decoding the argument."
    # Bytes[maxLen] is ``bytes`` on the ABI level (docs/types.rst:358-359).
    c = get_contract("""
@external
def f(x: Bytes[4]) -> uint256:
    return len(x)
""")
    # enc((x,)) = offset 0x20, then enc(len) and the bytes right-padded to 32.
    at_bound = selector("f(bytes)") + word(0x20) + word(4) + b"abcd" + bytes(28)
    assert env.message_call(c.address, data=at_bound) == word(4)

    over_bound = selector("f(bytes)") + word(0x20) + word(5) + b"abcde" + bytes(27)
    with tx_failed():
        env.message_call(c.address, data=over_bound)


def test_dynarray_argument_over_bound_reverts(env, get_contract, tx_failed):
    # docs/types.rst:548 at VYPER_PIN, Dynamic Arrays note: "Attempting to pass an array in
    # calldata which is larger than the array bound will result in a runtime ``REVERT``."
    c = get_contract("""
@external
def f(x: DynArray[uint8, 2]) -> uint256:
    return len(x)
""")
    # DynArray[uint8, 2] is uint8[]: offset 0x20, then enc(k) and k words.
    at_bound = selector("f(uint8[])") + word(0x20) + word(2) + word(1) + word(2)
    assert env.message_call(c.address, data=at_bound) == word(2)

    over_bound = selector("f(uint8[])") + word(0x20) + word(3) + word(1) + word(2) + word(3)
    with tx_failed():
        env.message_call(c.address, data=over_bound)
