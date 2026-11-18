# `self.is_contract` and `self.codehash` read the executing account like any
# address: EXTCODESIZE and EXTCODEHASH of `self`. The constructor runs before
# the runtime code is stored, so there `self` has no code yet.


def test_self_is_contract(get_contract):
    code = """
contract_at_deploy: bool
codehash_at_deploy: bytes32

@deploy
def __init__():
    self.contract_at_deploy = self.is_contract
    self.codehash_at_deploy = self.codehash

@external
@view
def contract_at_runtime() -> bool:
    return self.is_contract

@external
@view
def deploy_values() -> (bool, bytes32):
    return self.contract_at_deploy, self.codehash_at_deploy
    """
    c = get_contract(code)
    empty_codehash = bytes.fromhex(
        "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"
    )

    assert c.contract_at_runtime() is True
    assert c.deploy_values() == (False, empty_codehash)
