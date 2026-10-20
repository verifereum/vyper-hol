"""Finding 35: block.prevrandao translates to the randomness environment value."""

CONTRACT = """
@external
@view
def modern() -> bytes32:
    return block.prevrandao

@external
@view
def legacy() -> uint256:
    return block.difficulty

@external
@view
def number_control() -> uint256:
    return block.number
"""


def test_prevrandao_is_an_accepted_environment_property(get_contract):
    contract = get_contract(CONTRACT)
    # The checked local environment initializes PREVRANDAO to zero. The semantic
    # issue is translation of the accepted property, not the chosen block value.
    assert contract.modern() == bytes(32)
    assert contract.legacy() == 0
    assert contract.number_control() >= 0
