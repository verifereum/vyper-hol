"""Finding 23: a child created and destroyed in one transaction is deleted."""

CONTRACT = r"""
@external
def create_and_destroy() -> address:
    child: address = raw_create(
        b"\x60\x04\x60\x0c\x60\x00\x39\x60\x04\x60\x00\xf3\x61\x01\x23\xff",
        value=10,
    )
    raw_call(child, b"")
    return child
"""


def test_creation_history_survives_nested_call_boundary(get_contract, env):
    factory = get_contract(CONTRACT)
    beneficiary = "0x0000000000000000000000000000000000000123"
    beneficiary_balance = env.get_balance(beneficiary)
    env.set_balance(factory.address, 100)

    child = factory.create_and_destroy()

    assert env.get_balance(factory.address) == 90
    assert env.get_balance(beneficiary) == beneficiary_balance + 10
    assert env.get_balance(child) == 0
    # The differential runner's full checkpoint, rather than env.get_code,
    # verifies that the deleted child's account and code are absent.
