"""Execute both independent and HOL runtimes for construction regressions."""
from pathlib import Path
from eth.chains.base import MiningChain
from eth.db.atomic import AtomicDB
from eth.vm.forks.prague import PragueVM
from eth_abi import encode, decode
from eth_utils import keccak

here = Path(__file__).resolve().parent
chain_type = MiningChain.configure(__name__='ConstructionChain', vm_configuration=((0, PragueVM),))
cases = [
    ('c10_assign_empty_struct', 'f(uint256)', ['uint256'], [7], ['uint256'], (0,)),
    ('c11_annassign_empty_fixed_array', 'f(uint256)', ['uint256'], [7], ['uint256'], (7,)),
    ('empty_string_ret', 'f()', [], [], ['string'], ('',)),
    ('c05_assign_empty_builtin_string', 'f()', [], [], ['string'], ('',)),
    ('empty_dynarr_local', 'f(uint256)', ['uint256'], [7], ['uint256[]'], ((),)),
    ('arr_local_elem_assign', 'f(uint256)', ['uint256'], [7], ['uint256[3]'], ((0, 7, 0),)),
    ('st_empty_ret', 'f()', [], [], ['(string,uint256)'], (('', 0),)),
    ('tup_nested_ret', 'f(uint256)', ['uint256'], [7], ['uint256', '(uint256,bool)'], (7, (7, True))),
]
for name, signature, in_types, args, out_types, expected in cases:
    for label, root in [('Vyper', here / 'memory-stores/oracle'), ('HOL', here / 'memory-construction-results')]:
        runtime = dict(line.split('=', 1) for line in (root / (name + '.hex')).read_text().splitlines())['runtime']
        chain = chain_type.from_genesis(AtomicDB(), {'difficulty': 0, 'gas_limit': 10_000_000, 'timestamp': 1}, {})
        result = chain.get_vm().execute_bytecode(origin=b'\x01'*20, sender=b'\x01'*20,
            to=b'\x02'*20, gas_price=0, gas=1_000_000, value=0,
            data=keccak(text=signature)[:4] + encode(in_types, args), code=bytes.fromhex(runtime))
        if result.is_error:
            raise RuntimeError((name, label, result.error))
        actual = decode(out_types, result.output)
        print(name, label, actual, flush=True)
        if actual != expected:
            raise AssertionError((name, label, actual, expected))
