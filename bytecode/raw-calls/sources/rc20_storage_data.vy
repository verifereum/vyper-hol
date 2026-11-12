# raw_call with storage Bytes data
s: Bytes[40]
@external
def foo(t: address):
    raw_call(t, self.s)
