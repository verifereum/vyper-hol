# a10: x in 2-element literal list (control for fold order)
@external
def f(x: uint256) -> bool:
    return x in [1, 2]
