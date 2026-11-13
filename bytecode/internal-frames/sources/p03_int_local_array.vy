# internal function with a fixed-array local
@internal
def bar(y: uint256) -> uint256:
    a: uint256[3] = [y, y + 1, y + 2]
    return a[1]

@external
def foo(x: uint256) -> uint256:
    return self.bar(x)
