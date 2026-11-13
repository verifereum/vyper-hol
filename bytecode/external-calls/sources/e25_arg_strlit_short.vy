# string literal argument shorter than the declared parameter bound
interface Peer:
    def set_name(s: String[40]): nonpayable

@external
def f(t: address):
    extcall Peer(t).set_name("abc")
