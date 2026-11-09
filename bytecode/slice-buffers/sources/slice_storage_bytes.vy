# slice of storage Bytes
b: Bytes[50]
@external
@view
def f() -> Bytes[10]:
    return slice(self.b, 1, 10)
