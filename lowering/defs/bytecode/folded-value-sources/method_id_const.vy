SIG: constant(String[10]) = "foo()"
@external
@pure
def f() -> bytes4:
    return method_id(SIG, output_type=bytes4)
