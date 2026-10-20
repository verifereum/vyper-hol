# argument named __return_pc__ of an internal function (#557, a04-04)
@internal
def g(__return_pc__: uint256) -> uint256:
    return __return_pc__

@external
def f() -> uint256:
    return self.g(4)
