# String[5] argument for a String[40] parameter
interface Peer:
    def set_name(s: String[40]): nonpayable

@external
def f(t: address, s: String[5]):
    extcall Peer(t).set_name(s)
