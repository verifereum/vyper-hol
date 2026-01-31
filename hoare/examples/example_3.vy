# Example 3

@external
def example_3(x_arg: uint256) -> uint256:
    x: uint256 = x_arg
    x += 10
    if x > 100:
       x = 100
    else:
       x += 10
    if x > 20:
      return x
    y: uint256 = x + 20
    return y
