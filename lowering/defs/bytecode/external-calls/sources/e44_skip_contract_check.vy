# extcall of a void function with skip_contract_check=True: no extcodesize check
interface Peer:
    def put(x: uint256): nonpayable

@external
def f(t: address, x: uint256):
    extcall Peer(t).put(x, skip_contract_check=True)
