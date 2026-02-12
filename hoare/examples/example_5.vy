# Example 5: for range

@external
def example_5(n: uint256) -> uint256:
    s: uint256 = 0
    for i:uint256 in range(n, bound=1000000):
        s += i
    return s
