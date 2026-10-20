# internal function with a DynArray local
@internal
def bar(y: uint256) -> uint256:
    a: DynArray[uint256, 3] = [y]
    a.append(y + 1)
    return len(a)

@external
def foo(x: uint256) -> uint256:
    return self.bar(x)
