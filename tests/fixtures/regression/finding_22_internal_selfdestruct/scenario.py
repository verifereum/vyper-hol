"""Finding 22: selfdestruct terminates the whole call from an internal function."""

CONTRACT = """
marker: public(uint256)

@internal
def destroy():
    selfdestruct(0x0000000000000000000000000000000000001234)

@external
def run():
    self.destroy()
    self.marker = 7
"""


def test_internal_selfdestruct_skips_the_caller_remainder(get_contract, env):
    contract = get_contract(CONTRACT)
    beneficiary = "0x0000000000000000000000000000000000001234"
    beneficiary_balance = env.get_balance(beneficiary)
    env.set_balance(contract.address, 10)

    contract.run()

    assert env.get_balance(beneficiary) == beneficiary_balance + 10
    assert contract.marker() == 0
