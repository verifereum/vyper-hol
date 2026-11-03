# libp: stateless helper module (types, constants, pure internal functions)
struct P:
    a: uint256
    b: uint256

flag F:
    X
    Y
    Z

interface IFoo:
    def foo(x: uint256) -> uint256: view
    def bar(x: uint256): nonpayable

event Ev:
    who: indexed(address)
    v: uint256

K: constant(uint256) = 7
KS: constant(String[5]) = "hello"

@internal
@pure
def add(x: uint256) -> uint256:
    return x + K

@internal
@pure
def mkp(x: uint256) -> P:
    return P(a=x, b=x + 1)

@internal
@pure
def fsel(x: uint256) -> F:
    if x == 0:
        return F.X
    return F.Z
