
@external
def run() -> uint256[2]:
    indices: DynArray[uint256, 2] = [0, 1]
    result: uint256[2] = [7, 8]

    # RHS indices.pop() returns 1 and leaves [0]. Resolving the target next
    # pops 0, so the assignment is result[0] = 1.
    result[indices.pop()] = indices.pop()
    return result
