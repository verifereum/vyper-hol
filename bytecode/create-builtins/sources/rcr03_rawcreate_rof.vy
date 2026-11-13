# raw_create revert_on_failure=False
@external
def foo(b: Bytes[100]) -> address:
    return raw_create(b, revert_on_failure=False)
