m: bytes4
@external
def f():
    self.m = method_id("foo()", output_type=bytes4)
