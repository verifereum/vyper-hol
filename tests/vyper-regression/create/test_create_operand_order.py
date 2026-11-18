"""Creation builtins evaluate constructor arguments before value=, salt= and
code_offset=, and read each constructor argument when it is evaluated."""

CHILD = """
first: public(uint256)
second: public(uint256)

@deploy
def __init__(a: uint256, b: uint256):
    self.first = a
    self.second = b
"""

FACTORY = """
order: public(DynArray[uint256, 8])
counter: public(uint256)

@internal
def mark(i: uint256) -> uint256:
    self.order.append(i)
    return 0

@internal
def bump() -> uint256:
    self.counter += 1
    return 0

@external
def raw_order(initcode: Bytes[100]) -> address:
    return raw_create(
        initcode,
        self.mark(1),
        self.mark(2),
        value=self.mark(3),
        salt=convert(self.mark(4), bytes32),
        revert_on_failure=False,
    )

@external
def blueprint_order(target: address) -> address:
    return create_from_blueprint(
        target,
        self.mark(1),
        self.mark(2),
        value=self.mark(3),
        salt=convert(self.mark(4), bytes32),
        code_offset=self.mark(5) + 3,
    )

@external
def blueprint_later_arg_mutates(target: address) -> address:
    return create_from_blueprint(target, self.counter, self.bump())

@external
def blueprint_salt_mutates(target: address) -> address:
    return create_from_blueprint(
        target, self.counter, self.counter + 7, salt=convert(self.bump(), bytes32)
    )
"""


def test_raw_create_evaluates_constructor_arguments_first(get_contract):
    factory = get_contract(FACTORY)
    factory.raw_order(b"")
    assert factory.order(0) == 1
    assert factory.order(1) == 2
    assert factory.order(2) == 3
    assert factory.order(3) == 4


def test_blueprint_evaluates_constructor_arguments_first(
    get_contract, deploy_blueprint_for
):
    blueprint, _ = deploy_blueprint_for(CHILD)
    factory = get_contract(FACTORY)
    factory.blueprint_order(blueprint.address)
    assert [factory.order(i) for i in range(5)] == [1, 2, 3, 4, 5]


def test_constructor_argument_is_read_when_evaluated(
    get_contract, deploy_blueprint_for
):
    blueprint, Child = deploy_blueprint_for(CHILD)
    factory = get_contract(FACTORY)
    child = Child(factory.blueprint_later_arg_mutates(blueprint.address))
    assert child.first() == 0
    assert factory.counter() == 1


def test_constructor_argument_is_read_before_salt(get_contract, deploy_blueprint_for):
    blueprint, Child = deploy_blueprint_for(CHILD)
    factory = get_contract(FACTORY)
    child = Child(factory.blueprint_salt_mutates(blueprint.address))
    assert child.first() == 0
    assert child.second() == 7
    assert factory.counter() == 1
