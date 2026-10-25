# internal function named __entry (runtime unit entry label)
@internal
def __entry(y: uint256) -> uint256:
    return y + 1

@external
def foo(x: uint256) -> uint256:
    return self.__entry(x)
