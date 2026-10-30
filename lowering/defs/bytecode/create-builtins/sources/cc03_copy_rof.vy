# create_copy_of revert_on_failure=False
@external
def foo(t: address) -> address:
    return create_copy_of(t, revert_on_failure=False)
