@external
def minmax() -> decimal:
    return min(3.0, 5.0) + max(10.0, 20.0) + min(200.1, 400.0) + max(3000.0, 8000.02) + min(50000.003, 70000.004)

@external
def integer_minmax() -> uint256:
    return min(3, 5) + max(40, 80)

@external
def arithmetic() -> decimal:
    return (1.25 + 2.5) * 3.0 - 4.0 / 2.0

@external
def negative() -> decimal:
    return -(1.25 + 2.5)

@external
def scientific() -> decimal:
    return min(1.25e-2, 2.5e+1) + max(1e-10, 2e-10)

@external
def minimum() -> decimal:
    return min_value(decimal)

@external
def maximum() -> decimal:
    return max_value(decimal)
