#!/usr/bin/env python3
"""Independent Prague transaction tests for nested-place regression fixtures.

Expected values are literal TASK behaviours, never derived from HOL bytecode.
Each runtime starts from a fresh genesis; calls are signed transactions, not
execute_bytecode calls, so transaction-boundary transient cleanup is exercised.
"""
import json
import argparse
import hashlib
import tarfile
from pathlib import Path
from nested_place_behaviour_cases import (
    DEFERRED, INITIAL_STORAGE, RETURN_TYPES, full_cases, known_dependency_failure,
)

HERE = Path(__file__).resolve().parent / 'nested-places'

def execute(matrix=None, report=None, diagnostics=False, selected=None, full=False):
    from eth.chains.base import MiningChain
    from eth.db.atomic import AtomicDB
    from eth.vm.forks.prague import PragueVM
    from eth_keys import keys
    from eth_abi import encode, decode
    from eth_utils import keccak
    chain_type = MiningChain.configure(__name__='NestedPlaceChain', vm_configuration=((0, PragueVM),))
    private = keys.PrivateKey(b'\x01' * 32)
    sender = private.public_key.to_canonical_address()
    address = b'\x02' * 20
    def mapping(slot, key):
        # Vyper's storage mapping uses base slot followed by key.
        return int.from_bytes(keccak(slot.to_bytes(32, 'big') + key.to_bytes(32, 'big')), 'big')
    cases = [
        ('storage_struct_second_field', 'f()', [], [], 0, {}, {}),
        ('transient_struct_field', 'f(uint256)', ['uint256'], [5], 5, {}, {1: 5}),
        ('struct_field_named_like_storage', 'f()', [], [], 0, {2: 7}, {}),
        ('storage_2d_array', 'f(uint256,uint256,uint256)', ['uint256']*3, [1, 1, 9], 9, {3: 9}, {}),
        ('storage_nested_map', 'f(address,address,uint256)', ['address','address','uint256'],
         ['0x'+'00'*19+'01', '0x'+'00'*19+'02',9], 9, {mapping(mapping(0,1),2):9}, {}),
        ('storage_struct_array_field', 'f(uint256,uint256)', ['uint256']*2, [1,9],9,{2:9},{}),
        ('transient_hashmap','f(uint256,uint256)',['uint256']*2,[1,9],9,{}, {mapping(0,1):9}),
        ('s13_storage_map_of_array_elem','f(uint256,uint256,uint256)',['uint256']*3,[1,2,9],None,{mapping(0,1)+2:9},{}),
        ('s14_storage_map_of_struct_field','f(uint256,uint256)',['uint256']*2,[1,9],None,{mapping(0,1)+1:9},{}),
        ('s15_storage_map_string_key_assign','f(string,uint256)',['string','uint256'],['ab',9],9,
         {mapping(0,int.from_bytes(keccak(b'ab'),'big')):9},{}),
        ('s17_transient_map_assign','f(uint256,uint256)',['uint256']*2,[1,9],9,{}, {mapping(0,1):9}),
        ('x06_local_array_named_like_hashmap','f(uint256,uint256)',['uint256']*2,[1,9],1,{},{}),
    ]
    if matrix is not None:
        cases += [
            ('b05_nested_2d_elem', 'f(uint256,uint256,uint256)', ['uint256']*3,
             [1,1,9], 9, {}, {}),
            ('s25_nested_map_read_pure', 'f(address,address,uint256)',
             ['address','address','uint256'],
             ['0x'+'00'*19+'01', '0x'+'00'*19+'02',9], 9,
             {mapping(mapping(0,1),2):9}, {}),
            ('s19_nested_map_key_order', 'f(uint256)', ['uint256'], [9], None,
             {1:11, mapping(mapping(0,1),11):9, mapping(mapping(0,11),1):0}, {}),
            ('s20_nested_map_read_key_order', 'f()', [], [], 5,
             {1:11, mapping(mapping(0,1),11):5}, {}),
            ('arr_struct_subscript_attr_b', 'f((uint256,uint256)[],uint256)',
             ['(uint256,uint256)[]','uint256'], [[(10,11),(20,21)],1], 21, {}, {}),
            ('g5_hm_key_bytes', 'f(bytes,uint256)', ['bytes','uint256'],
             [bytes(range(40)),9], 9,
             {mapping(0,int.from_bytes(keccak(bytes(range(40))),'big')):9}, {}),
            ('g5_hm_key_string', 'f(string,uint256)', ['string','uint256'],
             ['ab',9], 9, {mapping(0,int.from_bytes(keccak(b'ab'),'big')):9}, {}),
            ('g4_t_hashmap_aug', 'f(address)', ['address'],
             ['0x'+'00'*19+'01'], 1, {}, {mapping(0,1):1}),
        ]
    if diagnostics:
        if matrix is None:
            raise ValueError('--diagnostics requires --matrix')
        cases = [case for case in cases if case[0] in
                 ('arr_struct_subscript_attr_b', 's20_nested_map_read_key_order',
                  'b05_nested_2d_elem')]
        cases += [
            ('b06_struct_arr_field_elem', 'f(uint256,uint256)', ['uint256']*2,
             [1,9], 9, {}, {}),
            ('g5_hm_val_array', 'f(uint256,uint256,uint256)', ['uint256']*3,
             [1,2,9], 9, {mapping(0,1)+2:9}, {}),
            ('g7_aug_transient_arr', 'f(uint256)', ['uint256'], [1], 1, {}, {1:1}),
            ('g5_hm_nested_aug', 'f(address,address,uint256)',
             ['address','address','uint256'],
             ['0x'+'00'*19+'01', '0x'+'00'*19+'02',3], None,
             {mapping(mapping(0,1),2):6}, {}),
        ]
    if selected is not None:
        cases = [case for case in cases if case[0] == selected]
        if not cases:
            raise ValueError(f'no behaviour case named {selected}')
    if full:
        if matrix is None or diagnostics or selected is not None:
            raise ValueError('--all requires --matrix and excludes --diagnostics/--case')
        cases = full_cases(cases, mapping, keccak)
        source_names = {path.stem for path in (HERE/'sources').glob('*.vy')}
        if {row[0] for row in cases} != source_names:
            raise ValueError('full behaviour table does not cover the supplied sources')
    def code_bytes(root, stem, kind='runtime'):
        if matrix is None:
            text = (root/(stem+'.hex')).read_text()
        else:
            member = ('oracle' if root.name == 'oracle' else 'actual')+'/'+stem+'.hex'
            with tarfile.open(matrix) as archive:
                text = archive.extractfile(member).read().decode()
        return bytes.fromhex(dict(line.split('=',1) for line in text.splitlines())[kind])
    def json_default(value):
        if isinstance(value, bytes):
            return '0x'+value.hex()
        raise TypeError(type(value).__name__)
    results = []
    for stem, signature, types, args, expected, storage, transient in cases:
        for label, root in [('Vyper',HERE/'oracle'),('HOL',HERE/'actual')]:
            row = {'witness':stem,'runtime':label}
            try:
                code = code_bytes(root, stem)
                row['runtime_sha256'] = hashlib.sha256(code).hexdigest()
                if transient or stem.startswith('x06'):
                    # Decode instructions rather than scanning PUSH payload bytes.
                    pc = 0
                    while pc < len(code):
                        opcode = code[pc]
                        if opcode == 0x55:
                            raise ValueError('persistent SSTORE in transient/local-only runtime')
                        pc += 1 + (opcode - 0x5f if 0x60 <= opcode <= 0x7f else 0)
                initial_storage = {mapping(mapping(0,1),2):9} if stem == 'g5_hm_nested_aug' else {}
                if full:
                    initial_storage.update(INITIAL_STORAGE.get(stem, {}))
                case_address = address
                first_nonce = 0
                chain = chain_type.from_genesis(AtomicDB(),
                    {'difficulty':0,'gas_limit':30_000_000,'timestamp':1,'base_fee_per_gas':0},
                    {sender:{'balance':10**20,'nonce':0,'code':b'','storage':{}},
                     address:{'balance':0,'nonce':0,
                              'code':b'' if stem == 'm10_imm_nested_array' else code,
                              'storage':initial_storage}})
                if stem == 'm10_imm_nested_array':
                    from eth._utils.address import generate_contract_address
                    creation = chain.get_vm().create_unsigned_transaction(nonce=0,gas_price=1,
                        gas=4_000_000,to=b'',value=0,data=code_bytes(root,stem,'deploy'))
                    _, _, deployed = chain.apply_transaction(creation.as_signed_transaction(private))
                    if deployed.is_error:
                        raise ValueError(f'deployment failed: {deployed.error}')
                    case_address = generate_contract_address(sender,0)
                    deployed_code = chain.get_vm().state.get_code(case_address)
                    if not deployed_code:
                        raise ValueError('deployment produced empty runtime')
                    row['deployed_runtime_sha256'] = hashlib.sha256(deployed_code).hexdigest()
                    first_nonce = 1
                calldata = keccak(text=signature)[:4] + encode(types,args)
                def call(nonce, data=None, expect_revert=False):
                    tx = chain.get_vm().create_unsigned_transaction(nonce=nonce,gas_price=1,
                        gas=2_000_000,to=case_address,value=0,
                        data=calldata if data is None else data).as_signed_transaction(private)
                    _, _, computation = chain.apply_transaction(tx)
                    if computation.is_error and not expect_revert:
                        raise ValueError(str(computation.error))
                    if expect_revert and not computation.is_error:
                        raise ValueError('expected revert, transaction succeeded')
                    return computation
                if stem == 'f38_for_storage_struct_field_arr_set':
                    call(first_nonce,keccak(text='set(uint256)')[:4]+encode(['uint256'],[9]))
                    first_nonce += 1
                return_types = RETURN_TYPES.get(stem,['uint256'])
                def returned(computation):
                    if expected is None:
                        if computation.output:
                            raise ValueError('void function returned data')
                        return None
                    values = decode(return_types,computation.output)
                    return values[0] if len(return_types) == 1 else values
                computation = call(first_nonce)
                actual = returned(computation)
                if actual != expected: raise ValueError(f'return {actual}, expected {expected}')
                state = chain.get_vm().state
                for slot,value in storage.items():
                    if state.get_storage(case_address,slot) != value:
                        raise ValueError(f'persistent slot {slot}: {state.get_storage(case_address,slot)} != {value}')
                # Explicitly reject accidental SSTORE in transient/collision tests.
                for slot in set(transient) | ({mapping(0,1)} if stem.startswith('x06') else set()):
                    if state.get_storage(case_address,slot) != 0: raise ValueError('unexpected persistent write')
                if transient:
                    # Check transaction cleanup directly, then repeat the real call.
                    # Augmentation must return 1 again rather than retaining 2.
                    for slot in transient:
                        if state.get_transient_storage(case_address,slot) not in (b'', b'\x00'*32):
                            raise ValueError('transient state survived completed transaction')
                    second = call(first_nonce+1)
                    second_return = returned(second)
                    if second_return != expected:
                        raise ValueError(f'second transaction return {second_return}, expected {expected}')
                bad_args = {
                    'b05_nested_2d_elem': [2,0,9],
                    'storage_2d_array': [3,0,9],
                    'arr_struct_subscript_attr_b': [[(10,11),(20,21)],2],
                    'g5_hm_nested_aug': ['0x'+'00'*19+'01', '0x'+'00'*19+'02',10],
                }.get(stem)
                if bad_args is not None:
                    call(first_nonce+1, keccak(text=signature)[:4] + encode(types,bad_args), expect_revert=True)
                    state = chain.get_vm().state
                    for slot,value in storage.items():
                        if state.get_storage(case_address,slot) != value:
                            raise ValueError('reverting transaction changed persistent state')
                row.update(status='PASS',returned=actual,storage={str(k):v for k,v in storage.items()},
                           transient_boundary=bool(transient),revert_checked=bad_args is not None)
            except Exception as error:
                row.update(status='ERROR',error=f'{type(error).__name__}: {error}')
                if full and label == 'HOL' and stem in DEFERRED:
                    try:
                        with tarfile.open(matrix) as archive:
                            stages = archive.extractfile(f'actual/{stem}.stages').read().decode().splitlines()
                    except (KeyError, OSError, tarfile.TarError):
                        stages = []
                    if stages and known_dependency_failure(stem,error,stages[-1]):
                        row.update(status='DEFERRED',reason=DEFERRED[stem])
            results.append(row)
            print(json.dumps(row,default=json_default),flush=True)
    output = Path(report) if report is not None else HERE/'actual/behaviour.json'
    output.write_text(json.dumps(results,indent=2,default=json_default)+'\n')
    if any(row['status'] not in ('PASS','DEFERRED') for row in results):
        raise ValueError('nested-place behaviour validation failed; see behaviour.json')

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--matrix', type=Path, help='Retained matrix archive; read without extraction')
    parser.add_argument('--report', type=Path)
    parser.add_argument('--diagnostics', action='store_true', help='Run the corrected diagnostic subset')
    parser.add_argument('--case', help='Run one named behaviour case')
    parser.add_argument('--all', action='store_true', help='Cover all supplied sources, with explicit conditional deferrals')
    args = parser.parse_args()
    execute(args.matrix, args.report, args.diagnostics, args.case, args.all)
