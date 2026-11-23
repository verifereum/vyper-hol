# A conditional expression and `|`, `&`, `^` on a flag have the type of their
# operands. When the operands are a flag imported from another module, so is
# the result, even if the current module declares a flag of the same name with
# fewer members: `~` over the result ranges over the imported flag's members.

FLAGS = """
flag F:
    M0
    M1
    M2
"""

CONTRACT = """
import flags as library

flag F:
    M0

@external
@pure
def inverted_choice(c: bool) -> uint256:
    return convert(~(library.F.M0 if c else library.F.M1), uint256)

@external
@pure
def inverted_argument_choice(c: bool, a: library.F, b: library.F) -> uint256:
    return convert(~(a if c else b), uint256)

@external
@pure
def inverted_or() -> uint256:
    return convert(~(library.F.M0 | library.F.M1), uint256)

@external
@pure
def inverted_and(a: library.F, b: library.F) -> uint256:
    return convert(~(a & b), uint256)

@external
@pure
def inverted_xor(a: library.F, b: library.F) -> uint256:
    return convert(~(a ^ b), uint256)

@external
@pure
def or_result(a: library.F, b: library.F) -> library.F:
    return a | b

@external
@pure
def choice_result(c: bool) -> library.F:
    return library.F.M2 if c else library.F.M0

@external
@pure
def in_xor(a: library.F, b: library.F) -> bool:
    return library.F.M2 in (a ^ b)
"""


def test_imported_flag_ifexp_binop(get_contract, make_input_bundle):
    bundle = make_input_bundle({"flags.vy": FLAGS})
    c = get_contract(CONTRACT, input_bundle=bundle)

    assert c.inverted_choice(True) == 6
    assert c.inverted_choice(False) == 5
    assert c.inverted_argument_choice(True, 1, 4) == 6
    assert c.inverted_argument_choice(False, 1, 4) == 3
    assert c.inverted_or() == 4
    assert c.inverted_and(3, 6) == 5
    assert c.inverted_xor(3, 6) == 2
    assert c.or_result(1, 4) == 5
    assert c.choice_result(True) == 4
    assert c.choice_result(False) == 1
    assert c.in_xor(3, 6) is True
    assert c.in_xor(5, 4) is False
