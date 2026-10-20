"""Finding 20: direct self account properties translate as account builtins."""

CONTRACT = """
@external
@view
def direct() -> (uint256, bytes32, bool, uint256):
    return self.codesize, self.codehash, self.is_contract, self.balance

@external
@view
def through_address(target: address) -> (uint256, bytes32, bool, uint256):
    return target.codesize, target.codehash, target.is_contract, target.balance
"""


def test_direct_self_properties_match_address_alias(get_contract, env):
    contract = get_contract(CONTRACT)
    env.set_balance(contract.address, 17)

    direct = contract.direct()
    assert direct == contract.through_address(contract.address)
    assert direct[0] > 0
    assert direct[2:] == (True, 17)
