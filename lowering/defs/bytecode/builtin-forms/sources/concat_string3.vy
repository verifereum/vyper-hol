# concat of three Strings incl a literal
@external
@pure
def f(a: String[10], b: String[5]) -> String[20]:
    return concat(a, " ", b)
