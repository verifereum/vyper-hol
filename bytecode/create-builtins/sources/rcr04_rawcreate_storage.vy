# raw_create with storage bytecode
s: Bytes[200]
@external
def foo() -> address:
    return raw_create(self.s)
