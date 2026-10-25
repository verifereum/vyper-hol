# storage String[5] argument for a String[40] parameter: read at the
# declared parameter type
interface Peer:
    def set_name(s: String[40]): nonpayable

s: String[5]

@external
def f(t: address):
    extcall Peer(t).set_name(self.s)
