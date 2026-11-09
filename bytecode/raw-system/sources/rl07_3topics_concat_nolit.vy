# raw_log with 3 topics (one computed) and concat data (no bytes literal)
@external
def foo(a: bytes32, b: bytes32):
    raw_log([a, b, keccak256(a)], concat(a, b))
