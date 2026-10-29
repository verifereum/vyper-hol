# control (no a08 builtin): concat(Bytes arg, bytes32) returned
@external
def foo(x: bytes32, d: Bytes[4]) -> Bytes[36]:
    return concat(d, x)
