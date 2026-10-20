"""Finding 21: event arguments follow each backend's evaluation order."""

CONTRACT = """
event Seen:
    data: uint256
    topic: indexed(uint256)

counter: uint256

@internal
def bump() -> uint256:
    self.counter += 1
    return self.counter

@external
def emit_values():
    self.counter = 0
    log Seen(data=self.bump(), topic=self.bump())
"""


def test_effectful_event_arguments(get_contract, get_logs, keccak, experimental_codegen):
    contract = get_contract(CONTRACT)
    contract.emit_values()

    topic, data = (2, 1) if experimental_codegen else (1, 2)
    assert get_logs(contract, raw=True) == [
        ([keccak(b"Seen(uint256,uint256)"), topic.to_bytes(32, "big")], data.to_bytes(32, "big"))
    ]
