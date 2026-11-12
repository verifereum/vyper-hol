# slice(self.code, ...)
@external
@view
def f() -> Bytes[10]:
    return slice(self.code, 0, 10)
