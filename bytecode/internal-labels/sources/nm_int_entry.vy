# internal function named __entry with no arguments
@internal
def __entry() -> uint256:
    return 1

@external
def g() -> uint256:
    return self.__entry()
