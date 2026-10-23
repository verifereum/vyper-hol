from pathlib import Path
import hashlib,json,re,subprocess
root=Path.cwd()
dest=root/'notes/validation/folded-value-2026-10-23'
base=root/'lowering/defs/bytecode'
report=json.loads((dest/'results.json').read_text())
rows={r['stem']:r for r in report['witnesses']}
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
stems=(base/'folded-value-witnesses.txt').read_text().split()
assert len(rows)==37 and set(rows)==set(stems)
for stem,row in rows.items():
    assert sha(base/'folded-value-sources'/(stem+'.vy'))==row['source_sha256']
    if stem=='method_id_var':
        assert row['verdict']=='EXPECTED_PYTHON_REJECTION' and row['python_ast_exit']!=0
        continue
    assert row['python_ast_exit']==row['python_bytecode_exit']==0
    assert row['check_runtime']==row['check_deploy']=='ACCEPT'
    assert sha(base/'folded-value-oracle'/(stem+'.json'))==row['ast_sha256']
    assert sha(base/'folded-value-oracle'/(stem+'.hex'))==row['oracle_sha256']
assert {s for s,r in rows.items() if r['verdict']=='BYTECODE_MISMATCH'}=={'ctl03_abi_method_id','enc_ensT_uint_mid','rc09_abi_encode_data','rr03_abi'}
assert {s for s,r in rows.items() if r['verdict']=='COMPILE_NONE'}=={'i12_immut_with_storage','p29_imm_multi'}
assert sum(r['verdict']=='MATCH' for r in rows.values())==30
parity=(base/'folded-value-parity-fixtures.txt').read_text().split()
assert len(parity)==7 and all(rows[s]['verdict']=='MATCH' for s in parity)
executions=json.loads((dest/'executions.json').read_text())
assert executions['engine_version']=='0.12.1b1'
seen=set()
for execution in executions['executions']:
    stem,label=execution['stem'],execution['producer']
    assert execution['reverted'] and execution['error_type']=='Revert'
    assert execution['runtime_sha256']==rows[stem][('python_' if label=='Python' else 'hol_')+'runtime_sha256']
    seen.add((stem,label))
assert seen=={(s,p) for s in ['pow_folded_exp','pow_negfold_base'] for p in ['Python','HOL']}
assert len(executions['executions'])==4
provenance=json.loads((base/'folded-value-oracle/provenance.json').read_text())
assert provenance['vyper_commit']==(root/'VYPER_PIN').read_text().strip()
assert provenance['python_version']=='3.11.11' and provenance['uv_version']=='0.10.11'
assert len(provenance['fixtures'])==36
assert provenance['settings']=={'experimental_codegen':True,'optimization_level':'NONE','venom_ir_pipeline':'O1','final_assembly_optimization':False,'evm_version':'prague','bytecode_metadata':False,'outputs':['bytecode','bytecode_runtime']}
assert 'all 101 Python O1/no-assembly-opt oracle fixtures reproduce from VYPER_PIN' in (dest/'corpus-python.log').read_text()
assert report['corpus']['status']=='COMPLETE' and report['corpus']['attempted']==report['corpus']['expected_targets']==33
for target,entry in json.loads((dest/'corpus/results.json').read_text()).items():
    assert not (entry['exit']!=0 and 'dependencies' in entry and not entry['dependencies']),('cancelled root lacks its own failure evidence',target)
assert report['seven_fixture_theory']['exit']==0
finalize=json.loads((dest/'finalize-status.json').read_text())
assert len(finalize)==2 and all(row['exit']==0 for row in finalize)
assert 'AUDIT PASS:' in (dest/'theorem-audit.log').read_text()
assert sha(base/'eval/foldedValueParityScript.sml')==report['parity_script_sha256']
changed=subprocess.check_output(['git','diff','HEAD','--name-only'],text=True).splitlines()
allowed=['lowering/defs/bytecode/folded-value-validation.md',
         'lowering/defs/bytecode/eval/foldedValueParityScript.sml',
         'lowering/defs/bytecode/folded-value-oracle/',
         'notes/validation/folded-value-2026-10-23/']
assert all(any(name==prefix or (prefix.endswith('/') and name.startswith(prefix)) for prefix in allowed) for name in changed),changed
status={'status':'PASS','witnesses':37,'matching_bytecode_pairs':30,'seven_parity_theorems':7,'genuine_overflow_reverts':4,'corpus':report['corpus'],'source_and_artifact_hashes':'verified','compiler_semantics_and_whitelist_changes':False}
(dest/'bundle-verification.json').write_text(json.dumps(status,indent=2)+'\n')
files=sorted(p for p in dest.rglob('*') if p.is_file() and p.name!='ARTIFACTS.sha256')
(dest/'ARTIFACTS.sha256').write_text(''.join(sha(p)+'  '+str(p.relative_to(dest))+'\n' for p in files))
print(json.dumps(status,indent=2))
