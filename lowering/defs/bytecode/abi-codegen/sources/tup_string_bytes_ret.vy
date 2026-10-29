# tuple mixing word and String return value
@external
@pure
def f(s: String[5]) -> (uint256, String[5], bool):
    return 1, s, True
