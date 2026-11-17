# pop() into a wider variable is typed at the element type.
arr: DynArray[Bytes[10], 3]

@external
def f() -> Bytes[100]:
    self.arr.append(b"cde")
    x: Bytes[100] = self.arr.pop()
    return x
