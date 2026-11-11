# a11: AnnAssign of b"" to a Bytes local (Vyper zero-length fast path)
@external
def f() -> uint256:
    b: Bytes[10] = b""
    return len(b)
