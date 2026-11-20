counter: uint256

error Failure:
    note: String[8]

@internal
def mutate() -> String[8]:
    self.counter += 1
    return "changed"

@internal
@view
def read() -> String[8]:
    return "read"

@external
def run(ok: bool):
    raise Failure(self.read())
