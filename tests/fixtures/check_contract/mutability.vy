# Mutability controls: each function here is accepted by Vyper.

interface Oracle:
    def price() -> uint256: view
    def poke(): nonpayable

event Poked:
    value: uint256

SCALE: constant(uint256) = 10
total: uint256
deposits: HashMap[address, uint256]
items: DynArray[uint256, 4]

@internal
@pure
def _scaled(x: uint256) -> uint256:
    return x * SCALE

@internal
@view
def _total() -> uint256:
    return self.total

@internal
@payable
def _paid() -> uint256:
    return msg.value

@external
@pure
def scaled(x: uint256) -> uint256:
    buf: DynArray[uint256, 4] = [x]
    buf.append(self._scaled(x))
    return buf.pop()

@external
@pure
def oracle_address(o: Oracle) -> address:
    return o.address

@external
@view
def view_calls(o: Oracle) -> uint256:
    return self._total() + self._scaled(staticcall o.price())

@external
@view
def view_reads(a: address, n: uint256 = block.number) -> uint256:
    return self.deposits[a] + self.balance + n + len(self.items)

@external
@view
def view_raw_call(a: address) -> Bytes[32]:
    return raw_call(a, b"", max_outsize=32, is_static_call=True)

@external
@view
@nonreentrant
def locked_view() -> uint256:
    return self.total

@external
@payable
def deposit() -> uint256:
    self.deposits[msg.sender] += self._paid()
    return msg.value

@external
def poke(o: Oracle):
    extcall o.poke()
    self.items.append(self._total())
    self.total = self.items.pop()
    log Poked(value=self.total)
