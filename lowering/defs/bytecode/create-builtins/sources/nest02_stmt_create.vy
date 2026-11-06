# create_copy_of result discarded? assigned to storage
a: address
@external
def foo(t: address):
    self.a = create_copy_of(t)
