# Example 2

@external
def example_2(x_arg: uint256):
    x: uint256 = x_arg
    x += 10
    if x > 100:
       x = 100
    else:
       x += 10
