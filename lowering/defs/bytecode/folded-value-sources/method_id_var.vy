@external
@pure
def f(s: String[30]) -> bytes4:
    return method_id(s, output_type=bytes4)
