# extcall returning String[32]
interface Peer:
    def name() -> String[32]: nonpayable

@external
def f(t: address) -> String[32]:
    return extcall Peer(t).name()
