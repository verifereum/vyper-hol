# extcall returning String[32] with a String default_return_value
interface Peer:
    def name() -> String[32]: nonpayable

@external
def f(t: address) -> String[32]:
    return extcall Peer(t).name(default_return_value="none")
