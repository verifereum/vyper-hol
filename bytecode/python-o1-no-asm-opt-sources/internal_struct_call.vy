struct Pair:
    left: uint256
    right: bytes32

@internal
@pure
def build_pair(left: uint256, right: bytes32) -> Pair:
    return Pair(left=left, right=right)

@external
@pure
def call_build_pair(left: uint256, right: bytes32) -> Pair:
    return self.build_pair(left, right)
