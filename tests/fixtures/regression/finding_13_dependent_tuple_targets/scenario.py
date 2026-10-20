"""Finding 13: tuple assignment resolves each target after earlier writes."""

CONTRACT = """
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
"""


def test_later_tuple_target_uses_updated_index(get_contract):
    assert get_contract(CONTRACT).run() == [1, 10, 7]
