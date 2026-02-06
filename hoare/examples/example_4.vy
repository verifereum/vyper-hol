# Example 4: lists and subscripts

@external
def example_4(x: uint256) -> int128:
    exampleList: int128[3] = [10, 11, 12]
    y: uint256 = x % 3
    exampleList[y] = exampleList[2 - y] + 7
    return exampleList[y]
    # {result >= 17 /\ result <= 19 }
