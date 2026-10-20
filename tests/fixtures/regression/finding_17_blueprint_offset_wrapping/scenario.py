"""Finding 17: blueprint code offsets wrap in uint256 arithmetic."""

CONTRACT = r"""
blueprint: public(address)

@deploy
def __init__():
    self.blueprint = raw_create(b"\x60\xfe\x60\x00\x53\x60\x01\x60\x00\xf3")

@external
def create(salt: bytes32) -> address:
    return create_from_blueprint(
        self.blueprint,
        code_offset=max_value(uint256),
        salt=salt,
        revert_on_failure=False,
    )
"""


def test_maximum_offset_copies_two_wrapped_zero_bytes(get_contract, env, keccak):
    factory = get_contract(CONTRACT)
    salt = bytes(32)
    expected = keccak(
        b"\xff"
        + bytes.fromhex(factory.address[2:])
        + salt
        + keccak(bytes(2))
    )[-20:]

    child = factory.create(salt)
    assert bytes.fromhex(child[2:]) == expected
    assert env.get_code(child) == b""
