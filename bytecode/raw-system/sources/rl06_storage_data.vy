# raw_log with storage Bytes data and storage bytes32 topic
s: Bytes[40]
t: bytes32
@external
def foo():
    raw_log([self.t], self.s)
