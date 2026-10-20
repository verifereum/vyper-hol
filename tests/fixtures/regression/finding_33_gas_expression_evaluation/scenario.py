"""Finding 33: gas keyword expressions retain effects and exceptions."""

TARGET = """
@external
@pure
def answer() -> uint256:
    return 42
"""

CALLER = """
interface Answer:
    def answer() -> uint256: view

count: uint256

@internal
def budget() -> uint256:
    self.count += 1
    return 100000

@external
def call_with_effect(target: address) -> (uint256, uint256):
    self.count = 0
    result: uint256 = staticcall Answer(target).answer(gas=self.budget())
    return result, self.count

@external
@view
def call_with_divisor(target: address, divisor: uint256) -> uint256:
    return staticcall Answer(target).answer(gas=100000 // divisor)
"""


def test_gas_expression_storage_effect_is_not_discarded(get_contract):
    target = get_contract(TARGET)
    caller = get_contract(CALLER)
    assert caller.call_with_effect(target.address) == (42, 1)


def test_gas_expression_error_is_not_discarded(get_contract, tx_failed):
    target = get_contract(TARGET)
    caller = get_contract(CALLER)
    with tx_failed():
        caller.call_with_divisor(target.address, 0)
    assert caller.call_with_divisor(target.address, 1) == 42
