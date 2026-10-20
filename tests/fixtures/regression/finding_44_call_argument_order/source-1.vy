
interface Callee:
    def accept(item: uint256): payable

order: public(uint256)

@internal
def mark_arg() -> uint256:
    self.order = self.order * 10 + 1
    return 7

@internal
def mark_value() -> uint256:
    self.order = self.order * 10 + 2
    return 0

@external
def run(callee: address):
    self.order = 0
    extcall Callee(callee).accept(self.mark_arg(), value=self.mark_value())
