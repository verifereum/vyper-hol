LOW: constant(int8) = min_value(int8)

@external
@pure
def low(xs: int8[max_value(int8)]) -> int8:
    return LOW
