"""Finding 39: self.code in a constructor is the executing initcode."""

CONTRACT = """
first_byte: immutable(Bytes[1])

@deploy
def __init__():
    self.first_byte = slice(self.code, 0, 1)

@external
@view
def saved() -> Bytes[1]:
    return self.first_byte
"""


def test_constructor_reads_its_initialization_code(get_contract, experimental_codegen):
    contract = get_contract(CONTRACT)
    # Current pinned backends begin initcode with PUSH1 (legacy) or CALLVALUE
    # (experimental O2). Both are exact observations from the retained report.
    expected = b"\x34" if experimental_codegen else b"\x60"
    assert contract.saved() == expected
