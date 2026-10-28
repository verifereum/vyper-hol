from .. import lib_a as a
initializes: a
from .. import lib_b
initializes: lib_b[lib_a := a]

exports: (lib_b.act, lib_b.counter, a.owner)

@deploy
def __init__():
    a.__init__()
