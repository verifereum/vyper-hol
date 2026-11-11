# control for i09: .address of an interface-typed local, no external call
interface Other:
    def ping(): nonpayable

@external
@view
def f(t: address) -> address:
    o: Other = Other(t)
    return o.address
