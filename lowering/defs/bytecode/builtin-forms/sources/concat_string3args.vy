# concat of three String args (no literal)
@external
@pure
def f(a: String[10], b: String[5], c: String[3]) -> String[18]:
    return concat(a, b, c)
