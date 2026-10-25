# DynArray[uint256, 2] argument for a DynArray[uint256, 8] parameter
interface Peer:
    def put(xs: DynArray[uint256, 8]): nonpayable

@external
def f(t: address, xs: DynArray[uint256, 2]):
    extcall Peer(t).put(xs)
