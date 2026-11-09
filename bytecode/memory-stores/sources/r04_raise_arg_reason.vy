# a11: raise with a calldata String argument as reason
@external
def f(s: String[30]):
    raise s
