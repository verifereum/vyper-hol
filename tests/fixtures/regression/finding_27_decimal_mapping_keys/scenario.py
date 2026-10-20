"""Finding 27: decimal values retain their scaled identity as mapping keys."""

from dataclasses import replace


CONTRACT = """
values: HashMap[decimal, uint256]
nested: HashMap[uint256, HashMap[decimal, uint256]]

@external
def direct() -> uint256[4]:
    self.values[1.0] = 11
    self.values[2.0] = 22
    self.values[-1.5] = 33
    return [self.values[1.0], self.values[2.0], self.values[-1.5], self.values[0.0]]

@external
def through_outer_key() -> uint256[4]:
    self.nested[7][1.0] = 11
    self.nested[7][2.0] = 22
    self.nested[8][1.0] = 33
    return [self.nested[7][1.0], self.nested[7][2.0], self.nested[8][1.0], self.nested[8][0.0]]
"""


def test_decimal_mapping_keys_do_not_alias(get_contract, compiler_settings):
    settings = replace(compiler_settings, enable_decimals=True)
    contract = get_contract(CONTRACT, compiler_settings=settings)
    assert contract.direct() == [11, 22, 33, 0]
    assert contract.through_outer_key() == [11, 22, 33, 0]
