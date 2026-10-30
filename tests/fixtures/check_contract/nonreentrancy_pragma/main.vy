# pragma nonreentrancy on

count: uint256

@external
def increment():
    self.count += 1

@external
@view
def get() -> uint256:
    return self.count

@external
@pure
def double(x: uint256) -> uint256:
    return 2 * x
