# a11: a: uint256[3] = empty(uint256[3]) after other memory use (complex empty() value)
@external
def f(x: uint256) -> uint256:
    b: uint256[3] = [x, x, x]
    a: uint256[3] = empty(uint256[3])
    return a[1] + b[0]
