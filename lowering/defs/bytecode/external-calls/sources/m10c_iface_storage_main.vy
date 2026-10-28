# a16 m10c_iface_storage_main: control for m10 with a main-module interface as the storage variable type
interface IFoo:
    def foo(x: uint256) -> uint256: view
    def bar(x: uint256): nonpayable

t: IFoo

@external
def f(a: address, x: uint256) -> uint256:
    self.t = IFoo(a)
    return staticcall self.t.foo(x)
