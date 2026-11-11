# raw_revert with storage Bytes data
s: Bytes[40]
@external
def foo():
    raw_revert(self.s)
