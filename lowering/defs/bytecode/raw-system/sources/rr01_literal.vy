# raw_revert with literal data
@external
def foo():
    raw_revert(b"\xde\xad")
