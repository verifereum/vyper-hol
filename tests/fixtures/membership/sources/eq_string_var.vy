# a10: == on String memory args (keccak compare)
@external
def f(a: String[10], b: String[10]) -> bool:
    return a == b
