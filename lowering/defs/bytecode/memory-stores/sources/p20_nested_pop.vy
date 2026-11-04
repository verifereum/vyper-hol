struct S:
    b: uint256
    a: DynArray[uint256, 4]
s: S
t: DynArray[DynArray[uint256, 2], 2]
m: HashMap[uint256, DynArray[uint256, 3]]
@external
def f() -> uint256:
    x: DynArray[DynArray[uint256, 3], 2] = [[1, 2], [3]]
    y: S = S(b=6, a=[4, 5])
    z: DynArray[DynArray[DynArray[uint256, 2], 2], 2] = [[[7], [8, 9]]]
    self.s = S(b=10, a=[11, 12])
    self.t = [[13, 14]]
    self.m[1] = [15, 16]
    w: DynArray[uint256, 2] = z[0].pop()
    return x[0].pop() + y.a.pop() + self.s.a.pop() + self.t[0].pop() + self.m[1].pop() + w[0]
