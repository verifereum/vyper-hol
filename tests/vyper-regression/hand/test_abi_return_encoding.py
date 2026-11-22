"""Return values encoded as the ABI specification says, with expected bytes written by hand.

Rule for every case: the Solidity ABI specification, "Function Selector and
Argument Encoding": return values ``v_1, ..., v_k`` are encoded as
``enc((v_1, ..., v_k))``; ``enc`` is defined in "Formal Specification of the
Encoding" (https://docs.soliditylang.org/en/latest/abi-spec.html). Vyper's ABI
type names are from docs/types.rst at VYPER_PIN (Bytes and String: lines 359 and 376;
DynArray: line 558).
"""

from eth_utils import keccak


def word(n: int) -> bytes:
    return n.to_bytes(32, "big")


def padded(data: bytes) -> bytes:
    # enc of bytes/string: the value followed by the fewest zero bytes making a multiple of 32.
    return data + bytes(-len(data) % 32)


def call(env, contract, signature: str) -> bytes:
    return env.message_call(contract.address, data=keccak(text=signature)[:4])


def test_static_tuple_is_heads_only(env, get_contract):
    # Static types are encoded in place: head(X(i)) = enc(X(i)), no tail.
    # uint<M>, address (as uint160) and bool (1 for true) are left-padded to 32 bytes.
    c = get_contract("""
@external
def f() -> (uint8, bool, address):
    return 7, True, 0x0000000000000000000000000000000000000123
""")
    assert call(env, c, "f()") == word(7) + word(1) + word(0x123)


def test_single_bytes_return_is_a_one_tuple(env, get_contract):
    # enc((X,)) for dynamic X: head = offset of its tail from the start (0x20),
    # tail = enc(X) = enc(len) pad_right(X).
    c = get_contract("""
@external
def f() -> Bytes[5]:
    return b"hello"
""")
    assert call(env, c, "f()") == word(0x20) + word(5) + padded(b"hello")


def test_dynamic_array_return(env, get_contract):
    # DynArray[uint256, 3] is uint256[] (docs/types.rst); enc(T[]) = enc(k) enc((X[0], ..., X[k-1])).
    c = get_contract("""
@external
def f() -> DynArray[uint256, 3]:
    return [1, 2, 3]
""")
    assert call(env, c, "f()") == word(0x20) + word(3) + word(1) + word(2) + word(3)


def test_mixed_tuple_offsets_count_from_tuple_start(env, get_contract):
    # Heads: 1, then the offsets of each tail from the start of the encoding.
    # Three heads take 0x60 bytes; the String tail takes 0x40, so the array tail starts at 0xa0.
    c = get_contract("""
@external
def f() -> (uint256, String[8], DynArray[uint8, 2]):
    return 1, "abc", [4, 5]
""")
    expected = (
        word(1) + word(0x60) + word(0xA0)
        + word(3) + padded(b"abc")
        + word(2) + word(4) + word(5)
    )
    assert call(env, c, "f()") == expected


def test_nested_dynamic_offsets_count_from_element_area(env, get_contract):
    # DynArray[Bytes[3], 2] is bytes[]: enc(k) followed by enc((X[0], X[1])), whose heads are
    # offsets from the start of that inner tuple, i.e. from just after the length word.
    c = get_contract("""
@external
def f() -> DynArray[Bytes[3], 2]:
    return [b"ab", b"xyz"]
""")
    expected = (
        word(0x20)
        + word(2) + word(0x40) + word(0x80)
        + word(2) + padded(b"ab")
        + word(3) + padded(b"xyz")
    )
    assert call(env, c, "f()") == expected


def test_single_dynamic_struct_return_is_a_one_tuple(env, get_contract):
    # docs/release-notes.rst:1086 at VYPER_PIN: "Change ABI encoding of single-struct return
    # values to be compatible with Solidity"; the ABI spec, "Mapping Solidity to ABI types":
    # a struct is a ``tuple``. So S returned alone is the only element of enc((S,)), and the
    # encoding starts with the 0x20 offset. Inside S, b's offset counts from S's start.
    c = get_contract("""
struct S:
    a: uint256
    b: Bytes[2]

@external
def f() -> S:
    return S(a=9, b=b"hi")
""")
    expected = word(0x20) + word(9) + word(0x40) + word(2) + padded(b"hi")
    assert call(env, c, "f()") == expected
