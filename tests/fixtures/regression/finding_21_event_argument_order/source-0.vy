
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
