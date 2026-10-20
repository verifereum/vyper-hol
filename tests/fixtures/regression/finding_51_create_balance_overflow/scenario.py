"""Finding 51: nonreverting CREATE2 reports recipient balance overflow as failure."""

from eth_utils import to_checksum_address
from hexbytes import HexBytes

FACTORY = """
@external
def attempt(salt: bytes32) -> address:
    return create_minimal_proxy_to(
        self,
        value=1,
        salt=salt,
        revert_on_failure=False,
    )
"""

SALT = (7).to_bytes(32, "big")


def _proxy_initcode(target):
    address = HexBytes(target)
    prefix = HexBytes("0x602D3D8160093D39F3363D3D373D3D3D363D73")
    suffix = HexBytes("0x5aF43D82803E903D91602B57FD5BF3")
    return prefix + address + suffix

def test_create_recipient_balance_overflow_is_soft_failure(
    get_contract, env, create2_address_of
):
    factory = get_contract(FACTORY)
    destination = to_checksum_address(
        create2_address_of(factory.address, SALT, _proxy_initcode(factory.address))
    )
    env.set_balance(factory.address, 1)
    env.set_balance(destination, 2**256 - 1)

    assert factory.attempt(SALT) == "0x0000000000000000000000000000000000000000"
    assert env.get_balance(factory.address) == 1
    assert env.get_balance(destination) == 2**256 - 1
