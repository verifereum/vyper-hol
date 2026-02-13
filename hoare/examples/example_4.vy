# Example 4: arrays and subscripts

@external
def example_4(x: uint256) -> int128:
    arr: int128[3] = [10, 11, 12]
    y: uint256 = x % 3
    arr[y] = arr[2 - y] + 7
    return arr[y]
    # {result >= 17 /\ result <= 19}
