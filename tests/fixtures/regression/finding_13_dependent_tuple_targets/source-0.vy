
@internal
@pure
def pair() -> (uint256, uint256):
    return 1, 7

@external
@pure
def run() -> uint256[3]:
    index: uint256 = 0
    values: uint256[2] = [10, 20]
    index, values[index] = self.pair()
    return [index, values[0], values[1]]
