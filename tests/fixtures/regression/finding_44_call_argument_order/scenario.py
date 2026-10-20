"""Finding 44: call boundaries preserve compiler operand evaluation order."""

TYPED_CALLEE = """
received: public(uint256)

@external
@payable
def accept(item: uint256):
    self.received = item
"""

TYPED_CALLER = """
interface Callee:
    def accept(item: uint256): payable

order: public(uint256)

@internal
def mark_arg() -> uint256:
    self.order = self.order * 10 + 1
    return 7

@internal
def mark_value() -> uint256:
    self.order = self.order * 10 + 2
    return 0

@external
def run(callee: address):
    self.order = 0
    extcall Callee(callee).accept(self.mark_arg(), value=self.mark_value())
"""

RAW_CALLEE = """
called: public(bool)

@external
def ping():
    self.called = True
"""

RAW_CALLER = """
order: public(uint256)

@internal
def mark_data() -> Bytes[4]:
    self.order = self.order * 10 + 1
    return method_id("ping()")

@internal
def mark_value() -> uint256:
    self.order = self.order * 10 + 2
    return 0

@external
def run(callee: address):
    self.order = 0
    raw_call(callee, self.mark_data(), value=self.mark_value())
"""

SEND_CALLER = """
order: public(uint256)

@internal
def mark_recipient(recipient: address) -> address:
    self.order = self.order * 10 + 1
    return recipient

@internal
def mark_amount() -> uint256:
    self.order = self.order * 10 + 2
    return 0

@external
def run(recipient: address):
    self.order = 0
    send(self.mark_recipient(recipient), self.mark_amount())
"""


def test_typed_call_packs_arguments_before_value(get_contract):
    callee = get_contract(TYPED_CALLEE)
    caller = get_contract(TYPED_CALLER)
    caller.run(callee.address)

    assert caller.order() == 12
    assert callee.received() == 7


def test_raw_call_backend_order(get_contract, experimental_codegen):
    callee = get_contract(RAW_CALLEE)
    caller = get_contract(RAW_CALLER)
    caller.run(callee.address)

    expected = 12 if experimental_codegen else 21
    assert caller.order() == expected
    assert callee.called() is True


def test_send_backend_order(get_contract, env, experimental_codegen):
    caller = get_contract(SEND_CALLER)
    caller.run(env.deployer)

    expected = 12 if experimental_codegen else 21
    assert caller.order() == expected
