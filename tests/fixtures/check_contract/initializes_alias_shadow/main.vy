import lib1
import lib3 as lib2
initializes: lib1.lib2
initializes: lib1
y: uint256

@external
def go() -> uint256:
    lib1.lib2.bump()
    return lib2.f()
