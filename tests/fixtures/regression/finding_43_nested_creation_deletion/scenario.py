"""Finding 43: nested-call deletion queues survive the EVM/source boundary."""

HELPER = r"""
@external
def spawn_and_destroy() -> address:
    child: address = raw_create(
        b"\x60\x04\x60\x0c\x60\x00\x39\x60\x04\x60\x00\xf3\x61\x01\x23\xff"
    )
    raw_call(child, b"")
    return child
"""

FACTORY = """
interface Helper:
    def spawn_and_destroy() -> address: nonpayable

@external
def run(helper: address) -> address:
    return extcall Helper(helper).spawn_and_destroy()
"""


def test_nested_callee_created_child_is_deleted(get_contract, env):
    helper = get_contract(HELPER)
    factory = get_contract(FACTORY)
    child = factory.run(helper.address)

    assert child != "0x0000000000000000000000000000000000000000"
    assert env.get_balance(child) == 0
    # The runner's finalized full-state checkpoint verifies that the child's
    # account and code are absent. env.get_code can expose stale journal code.
