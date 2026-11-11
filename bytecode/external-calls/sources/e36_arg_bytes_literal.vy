# bytes literal argument shorter than the declared parameter bound
interface Peer:
    def put(b: Bytes[40]): nonpayable

@external
def f(t: address):
    extcall Peer(t).put(b"\x01\x02")
