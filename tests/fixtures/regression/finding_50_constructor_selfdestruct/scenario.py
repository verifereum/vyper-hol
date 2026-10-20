"""Finding 50: SELFDESTRUCT in a top-level constructor removes the new account."""

CONTRACT = """
@deploy
def __init__():
    selfdestruct(msg.sender)

@external
@view
def marker() -> uint256:
    return 7
"""


def test_constructor_selfdestruct_leaves_no_runtime_account(get_contract, env):
    contract = get_contract(CONTRACT)
    assert env.get_code(contract.address) == b""
