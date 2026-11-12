# a call omitting defaults inside another one's arguments (f declared
# before g, the order pinned Python emits them in; function order is #546)
@internal
def f(x: uint256, y: uint256 = 4) -> uint256:
    return x * y

@internal
def g(x: uint256 = 2) -> uint256:
    return x + 1

@external
def nested() -> uint256:
    return self.f(self.g())
