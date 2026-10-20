
interface Reader:
    def read(target: address) -> uint256: view

entries: public(HashMap[bytes1, uint256])

@external
def through_callback(reader: address) -> uint256:
    self.entries[0x01] = 11
    return staticcall Reader(reader).read(self)
