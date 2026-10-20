
left: DynArray[uint256, 4]
right: DynArray[uint256, 4]

@internal
def mutate_left():
    self.left[1] = 90
    self.left.append(9)

@external
def probe(use_left: bool) -> uint256:
    self.left = [1, 2, 3]
    self.right = [4, 5, 6]
    result: uint256 = 0
    for item: uint256 in (self.left if use_left else self.right):
        result = result * 100 + item
        if item == 1:
            self.mutate_left()
    return result
