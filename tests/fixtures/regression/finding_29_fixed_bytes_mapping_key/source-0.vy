
interface Target:
    def entries(key: bytes1) -> uint256: view

@external
@view
def read(target: address) -> uint256:
    return staticcall Target(target).entries(0x01)
