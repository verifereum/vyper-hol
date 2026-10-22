# extcall with default_return_value and skip_contract_check=True
interface Peer:
    def get() -> bool: nonpayable

@external
def f(t: address) -> bool:
    return extcall Peer(t).get(default_return_value=True, skip_contract_check=True)
