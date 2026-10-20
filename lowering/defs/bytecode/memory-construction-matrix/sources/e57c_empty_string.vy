# empty(String[5]) as log arg after memory was dirtied
event E:
    a: String[5]

@external
def f(s: String[5]):
    log E(a=s)
    log E(a=empty(String[5]))
