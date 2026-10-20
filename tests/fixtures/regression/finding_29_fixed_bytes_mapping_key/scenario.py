"""Finding 29: source writes and compiled getters agree on fixed-byte map keys."""

TARGET = """
interface Reader:
    def read(target: address) -> uint256: view

entries: public(HashMap[bytes1, uint256])

@external
def through_callback(reader: address) -> uint256:
    self.entries[0x01] = 11
    return staticcall Reader(reader).read(self)
"""

READER = """
interface Target:
    def entries(key: bytes1) -> uint256: view

@external
@view
def read(target: address) -> uint256:
    return staticcall Target(target).entries(0x01)
"""


def test_compiled_callback_reads_source_written_slot(get_contract):
    reader = get_contract(READER)
    target = get_contract(TARGET)
    assert target.through_callback(reader.address) == 11
