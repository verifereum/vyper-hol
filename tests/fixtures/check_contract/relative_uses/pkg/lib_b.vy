from . import lib_a
uses: lib_a

counter: public(uint256)

@external
def act():
    lib_a._check()
    self.counter += 1
