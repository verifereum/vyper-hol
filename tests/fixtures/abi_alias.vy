# #551 blocker witness, accepted by pinned Vyper cd74ce4.
# Its late staging produces ([True], False), not the interpreter's
# materialised-argument result ([True, False], False).
@external
def alias() -> Bytes[160]:
    a: DynArray[bool, 2] = [True, False]
    return abi_encode(a, a.pop(), ensure_tuple=False)
