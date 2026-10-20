
first_byte: immutable(Bytes[1])

@deploy
def __init__():
    self.first_byte = slice(self.code, 0, 1)

@external
@view
def saved() -> Bytes[1]:
    return self.first_byte
