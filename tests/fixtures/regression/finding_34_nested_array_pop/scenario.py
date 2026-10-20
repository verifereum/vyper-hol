"""Finding 34: pop is a method on nested dynamic-array receivers."""

import pytest


CONTRACT = """
stored: DynArray[DynArray[uint256, 3], 2]

@external
def memory_pop(index: uint256) -> uint256[3]:
    values: DynArray[DynArray[uint256, 3], 2] = [[11, 22], [33, 44]]
    removed: uint256 = values[index].pop()
    values[index].append(55)
    return [removed, len(values[index]), values[index][1]]

@external
def storage_pop(index: uint256) -> uint256[3]:
    self.stored = [[11, 22], [33, 44]]
    removed: uint256 = self.stored[index].pop()
    self.stored[index].append(55)
    return [removed, len(self.stored[index]), self.stored[index][1]]
"""


@pytest.mark.parametrize("function", ["memory_pop", "storage_pop"])
@pytest.mark.parametrize("index,expected", [(0, [22, 2, 55]), (1, [44, 2, 55])])
def test_pop_from_indexed_nested_array(get_contract, function, index, expected):
    assert getattr(get_contract(CONTRACT), function)(index) == expected
