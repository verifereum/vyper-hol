import oracle
import lib
initializes: lib

@internal
@view
@override(lib)
def helper(target: oracle) -> uint256:
    return staticcall target.read_value(1)

@external
@view
def read(addr: address) -> uint256:
    return self.helper(oracle(addr))
