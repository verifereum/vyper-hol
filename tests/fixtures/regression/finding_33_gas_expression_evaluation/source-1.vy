
interface Answer:
    def answer() -> uint256: view

count: uint256

@internal
def budget() -> uint256:
    self.count += 1
    return 100000

@external
def call_with_effect(target: address) -> (uint256, uint256):
    self.count = 0
    result: uint256 = staticcall Answer(target).answer(gas=self.budget())
    return result, self.count

@external
@view
def call_with_divisor(target: address, divisor: uint256) -> uint256:
    return staticcall Answer(target).answer(gas=100000 // divisor)
