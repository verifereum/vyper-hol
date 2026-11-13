# create_copy_of basic
@external
def foo(t: address) -> address:
    return create_copy_of(t)
