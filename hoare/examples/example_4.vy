# Example 4: lists and subscripts

@external
def example_4(x: uint256) -> int128:
    exampleList: int128[3] = [10, 11, 12]
    exampleList[x % 3] += 7
    return exampleList[x % 3]
    # {result >= 17 /\ result <= 19 }
