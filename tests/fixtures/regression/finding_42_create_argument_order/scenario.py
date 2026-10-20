"""Finding 42: creation builtins preserve compiler argument evaluation order."""

RAW_FACTORY = r"""
order: public(uint256)
created: public(address)

@internal
def mark_arg() -> uint256:
    self.order = self.order * 10 + 1
    return 7

@internal
def mark_value() -> uint256:
    self.order = self.order * 10 + 2
    return 0

@internal
def mark_salt() -> bytes32:
    self.order = self.order * 10 + 3
    return empty(bytes32)

@external
def deploy() -> address:
    self.order = 0
    self.created = raw_create(
        b"\x60\x00\x60\x00\xf3",
        self.mark_arg(),
        value=self.mark_value(),
        salt=self.mark_salt(),
    )
    return self.created
"""

BLUEPRINT = """
stored: public(uint256)

@deploy
def __init__(initial: uint256):
    self.stored = initial
"""

BLUEPRINT_FACTORY = """
order: public(uint256)

@internal
def mark_arg() -> uint256:
    self.order = self.order * 10 + 1
    return 7

@internal
def mark_value() -> uint256:
    self.order = self.order * 10 + 2
    return 0

@internal
def mark_salt() -> bytes32:
    self.order = self.order * 10 + 3
    return empty(bytes32)

@internal
def mark_offset() -> uint256:
    self.order = self.order * 10 + 4
    return 3

@external
def deploy(blueprint: address) -> address:
    self.order = 0
    return create_from_blueprint(
        blueprint,
        self.mark_arg(),
        value=self.mark_value(),
        salt=self.mark_salt(),
        code_offset=self.mark_offset(),
    )
"""


def test_raw_create_evaluates_salt_before_constructor_arguments(get_contract, env):
    factory = get_contract(RAW_FACTORY)
    child = factory.deploy()

    assert child != "0x0000000000000000000000000000000000000000"
    assert factory.order() == 231
    assert env.get_code(child) == b""


def test_blueprint_evaluates_constructor_arguments_before_offset(
    get_contract, deploy_blueprint_for
):
    blueprint, Child = deploy_blueprint_for(BLUEPRINT)
    factory = get_contract(BLUEPRINT_FACTORY)
    child = Child(factory.deploy(blueprint.address))

    assert factory.order() == 2314
    assert child.stored() == 7
