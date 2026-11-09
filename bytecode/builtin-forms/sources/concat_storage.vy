# concat with a storage Bytes argument
b: Bytes[10]
@external
@view
def f(a: Bytes[5]) -> Bytes[15]:
    return concat(self.b, a)
