# raw_log with 3 topics and concat data
@external
def foo(a: bytes32, b: bytes32):
    raw_log([a, b, keccak256(b"x")], concat(a, b))
