
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
