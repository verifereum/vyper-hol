import lib
import lib3

initializes: lib
initializes: lib3

exports: (lib.IFace, lib3.__interface__)


@deploy
def __init__():
    lib.__init__()
