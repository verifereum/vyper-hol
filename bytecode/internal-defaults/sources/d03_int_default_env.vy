# defaults read the environment in the caller: msg.sender and an expression
# over block.timestamp
@internal
def f(a: address = msg.sender, t: uint256 = block.timestamp + 1) -> uint256:
    return convert(a, uint256) + t

@external
def omit() -> uint256:
    return self.f()
