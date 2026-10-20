
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
