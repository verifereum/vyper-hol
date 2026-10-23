from pathlib import Path
from collections import Counter
import csv, hashlib, json, re, shutil, subprocess

root=Path.cwd()
out=root/'.agent-files/folded-value-validation'
dest=root/'notes/validation/folded-value-2026-10-23'
dest.mkdir(parents=True,exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
exports=json.loads((out/'exports.json').read_text())
statuses={}
for line in (out/'hol/probe.log').read_text().splitlines():
    if line.startswith('WITNESS '):
        _,stem,message=line.split(' ',2)
        statuses.setdefault(stem,[]).append(message)
deps={
    'keccak_literal':'#569 bytestring hashing', 'len_string_lit':'#569 bytestring hashing',
    'ctl03_abi_method_id':'#551 ABI encode', 'enc_ensT_uint_mid':'#551 ABI encode',
    'i12_immut_with_storage':'#563 immutables', 'p29_imm_multi':'#563 immutables',
    'c16_const_string_in_expr':'#565 constants', 'c27_const_binop_fold':'#565 constants',
    'rc09_abi_encode_data':'#554/#551 ABI encoding', 'rr03_abi':'#567/#551 ABI encoding'}
rows=[]
for stem,export in exports.items():
    row={'stem':stem,'ast_sha256':None,'oracle_sha256':None,**export}
    messages=statuses.get(stem,[])
    def field(key,default='NOT_RUN'):
        return next((m.split('=',1)[1] for m in messages if m.startswith(key+'=')),default)
    row.update(frontend=field('FRONTEND'),check_runtime=field('CHECK_RUNTIME'),check_deploy=field('CHECK_DEPLOY'),supported_program=field('SUPPORTED'),compile=field('COMPILE'),error=field('ERROR',''),dependency_note=deps.get(stem,''))
    row.update(deploy_equal=None,runtime_equal=None)
    tops=out/'hol'/(stem+'.tops')
    row['translated_tops_sha256']=sha(tops) if tops.exists() else None
    if stem=='method_id_var':
        row['synthetic_hol_rejection']='vyperCheckContractLibTestTheory.check_contract_rejects_method_id_eval'
        for key in ('frontend','check_runtime','check_deploy','supported_program','compile'):
            row[key]='NOT_APPLICABLE_PYTHON_REJECTED'
    actual=out/'hol'/(stem+'.hex')
    expected=out/'oracle'/(stem+'.hex')
    if actual.exists() and expected.exists():
        def read(p):return {key:bytes.fromhex(value) for key,value in (line.split('=',1) for line in p.read_text().splitlines())}
        a,e=read(actual),read(expected)
        for mode in ('deploy','runtime'):
            row[mode+'_equal']=a[mode]==e[mode]
            row['hol_'+mode+'_sha256']=hashlib.sha256(a[mode]).hexdigest()
            row['python_'+mode+'_sha256']=hashlib.sha256(e[mode]).hexdigest()
            row['hol_'+mode+'_bytes']=len(a[mode])
            row['python_'+mode+'_bytes']=len(e[mode])
            row[mode+'_first_difference']=next((i for i,(x,y) in enumerate(zip(a[mode],e[mode])) if x!=y),min(len(a[mode]),len(e[mode])) if len(a[mode])!=len(e[mode]) else None)
    if stem=='method_id_var':row['verdict']='EXPECTED_PYTHON_REJECTION' if export['python_ast_exit']!=0 else 'UNEXPECTED_PYTHON_ACCEPT'
    elif export.get('python_ast_exit') or export.get('python_bytecode_exit'):row['verdict']='PYTHON_EXPORT_FAILURE'
    elif row['frontend']!='ACCEPT':row['verdict']='FRONTEND_FAILURE' if row['error'] else 'NOT_RUN'
    elif row['compile']=='NONE':row['verdict']='COMPILE_NONE'
    elif row['compile']=='RESIDUAL':row['verdict']='COMPILE_RESIDUAL'
    elif row['error']:row['verdict']='HOL_ERROR'
    elif row['deploy_equal'] is True and row['runtime_equal'] is True:row['verdict']='MATCH'
    elif row['compile']=='SOME':row['verdict']='BYTECODE_MISMATCH'
    else:row['verdict']='NOT_RUN'
    rows.append(row)
report={'source_revision':json.loads((out/'hol/run.json').read_text())['revision'],'scope':'37 exact source witnesses; independent pinned Python outputs; current checked HOL compilation; both deployment modes','byte_comparison':'Decoded byte arrays from checked HOL EVAL exports and independent Python oracle. Raw probe DEPLOY_EQUAL/RUNTIME_EQUAL lines compare unnormalised term syntax and are not byte equality verdicts. This report uses actual bytes.','verdict_counts':dict(Counter(r['verdict'] for r in rows)),'witnesses':rows}
corpus=json.loads((out/'corpus/results.json').read_text())
for target,entry in corpus.items():
    if entry['exit']!=0 and not entry.get('status'):
        candidates=[]
        for path in (root/'.holbuild/stage').glob('*/holbuild-build.log'):
            text=path.read_text()
            if 'Created theory "'+target.removesuffix('Theory')+'"' in text:
                candidates.append((path,text))
        if candidates:
            path,text=max(candidates,key=lambda item:item[0].stat().st_mtime)
            entry['status']='PROCESS_KILLED' if 'Killed' in text.splitlines()[-3:] else 'BUILD_FAILURE'
            entry['native_log']='native/'+target+'.log'
            if entry['status']=='PROCESS_KILLED':
                entry['detail']='Native log ends Killed; recorder did not stop this process. Cause unconfirmed.'
expected_targets=list(dict.fromkeys(re.findall(r'\bevalCompilerBytecode\w*Theory\b',(root/'lowering/defs/bytecode/python-o1-bytecode-fixtures').read_text())))
report['corpus']={'expected_targets':len(expected_targets),'attempted':sum(t in corpus for t in expected_targets),'passed':sum(corpus.get(t,{}).get('exit')==0 for t in expected_targets),'failures':{t:corpus[t] for t in expected_targets if t in corpus and corpus[t]['exit']!=0}}
report['corpus']['status']='COMPLETE' if report['corpus']['attempted']==len(expected_targets) else 'IN_PROGRESS'
report['parity_script_sha256']=sha(root/'lowering/defs/bytecode/eval/foldedValueParityScript.sml')
report['seven_fixture_theory']=corpus.get('foldedValueParityTheory',{'status':'RUNNING'})
(dest/'results.json').write_text(json.dumps(report,indent=2)+'\n')
fields=['stem','source_sha256','ast_sha256','oracle_sha256','frontend','check_runtime','check_deploy','supported_program','compile','deploy_equal','runtime_equal','verdict','dependency_note','error']
with (dest/'results.csv').open('w') as f:
    writer=csv.DictWriter(f,fields,extrasaction='ignore',lineterminator='\n');writer.writeheader();writer.writerows(rows)
for name in ('executions.json','executions.log','exports.json','corpus-python.log','corpus-hol.log','corpus-parallel.log','corpus-bounded.log','corpus-scheduled.log','corpus-retry-cancelled.log','provision.log','identity.json','theorem-audit.log','theorem-audit-first-attempt.log','command-exits.json','scheduler-switch.json','schedule-handoff.json','HANDOFF.md','prep-build.log','finalize-status.json'):
    p=out/name
    if p.exists():shutil.copyfile(p,dest/name)
for name in ('hol','corpus','logs','ast','single'):
    if (out/name).exists():shutil.copytree(out/name,dest/name,dirs_exist_ok=True)
(dest/'corpus/results.json').write_text(json.dumps(corpus,indent=2)+'\n')
runner=dest/'runner'
runner.mkdir(exist_ok=True)
for name in ('provision.py','export.py','probe.py','corpus.py','corpus_parallel.py','corpus_bounded.py','corpus_scheduled.py','corpus_retry_cancelled.py','execute.py','identity.py','report.py','finalize.py','verify_bundle.py'):
    archive_name=name+'.txt' if name in {'corpus_parallel.py','corpus_bounded.py','corpus_scheduled.py','corpus_retry_cancelled.py'} else name
    shutil.copyfile(out/name,runner/archive_name)
shutil.copyfile(root/'.folded_value_validation.sml',runner/'folded_value_validation.sml.txt')
shutil.copyfile(root/'.folded_value_audit.sml',runner/'folded_value_audit.sml.txt')
native=dest/'corpus/native'
native.mkdir(exist_ok=True)
selected_logs={}
dependency_logs=set()
for row in corpus.values():
    if row.get('dependency'):dependency_logs.add(row['dependency'])
    dependency_logs.update(row.get('dependencies',[]))
for path in (root/'.holbuild/stage').glob('*/holbuild-build.log'):
    content=path.read_text()
    match=re.search(r'Created theory "([^"]+)"',content)
    if match and (match[1]+'Theory' in corpus or match[1]+'Theory' in dependency_logs):
        name=match[1]+'Theory'
        if name not in selected_logs or path.stat().st_mtime>selected_logs[name].stat().st_mtime:
            selected_logs[name]=path
for name,path in selected_logs.items():
    shutil.copyfile(path,native/(name+'.log'))
(dest/'semantic-source-hashes.json').write_text(json.dumps({p:sha(root/p) for p in subprocess.check_output(['git','ls-files','frontend','lowering/defs','semantics/type'],text=True).splitlines() if (root/p).is_file()},indent=2)+'\n')
lines=['# Folded-value validation, 2026-10-23','',
       'Source revision: `'+report['source_revision']+'`. Vyper source: `~/vyper`, clean commit `'+(root/'VYPER_PIN').read_text().strip()+'`.',
       '', 'Independent artifacts are in `lowering/defs/bytecode/folded-value-oracle/`; all 36 accepted sources have AST/layout and deploy/runtime bytes. `method_id_var` is rejected by the pinned compiler with StructureException: Value must be a literal. The corresponding synthetic HOL rejection is `check_contract_rejects_method_id_eval`.',
       '', 'Toolchain: uv 0.10.11, managed CPython 3.11.11, Vyper 0.5.0a4+cd74ce4f. Settings: experimental codegen, optimize NONE (the pinned O1 Venom pipeline), Prague, no metadata. Dependency versions and source/byte hashes are in the independent provenance file.',
       '', 'The frozen Python corpus reproduced all 101 fixtures, plus memory-store and external-call subcorpora. Four actual py-evm 0.12.1b1 PragueVM executions reverted; calldata, bytecode hashes and gas use are in `executions.json`.',
       '', 'Counts: '+json.dumps(report['verdict_counts'])+'.',
       '', 'Full HOL corpus: '+json.dumps({key:value for key,value in report['corpus'].items() if key!='failures'})+'. Seven-fixture theory exit: '+str(report['seven_fixture_theory'].get('exit','pending'))+'. See corpus target outcomes below for failures.',
       '', '| Witness | Runtime/deploy checker | Supported | Compile | Deploy/runtime equal | Verdict | Dependency |',
       '|---|---|---|---|---|---|---|']
for r in rows:
    lines.append('| '+ ' | '.join(str(x) for x in [r['stem'],r['check_runtime']+'/'+r['check_deploy'],r['supported_program'],r['compile'],str(r['deploy_equal'])+'/'+str(r['runtime_equal']),r['verdict'],r['dependency_note']])+' |')
lines+=['','## Existing HOL corpus target outcomes','','| Target | Outcome |','|---|---|']
for target in expected_targets:
    entry=corpus.get(target)
    outcome='NOT_RUN' if entry is None else ('PASS' if entry['exit']==0 else entry.get('status','BUILD_FAILURE'))
    lines.append('| '+target+' | '+outcome+' |')
lines+=['','`results.json` and `results.csv` provide every source/AST/oracle identity and individual outcome. `hol/` retains translated tops, compiler EVAL results and emitted bytes. `logs/` retains each external command, exit status and stdout/stderr. `corpus/` retains each forced HOL corpus build.','', 'MATCH means both emitted byte arrays equal the independent Python outputs. It does not imply supported_program is true: that result is recorded separately, and current restrictions remain in force.','',report['byte_comparison'],'','No compiler semantics, whitelist restrictions (including Exp), frozen oracle data or existing proof statements were changed. The independent oracle is data; expected byte equalities were never installed as evaluator rewrite rules. Alan was not restarted.']
lines+=['','The #551 dependency is still present in this revision: `lowering/defs/builtinAbiScript.sml` defines `lower_abi_encode ensure_tuple ...` but never uses `ensure_tuple` in its body. The observed selector/tuple control mismatches are recorded as failures with this dependency, not as MATCH. The two immutable NONE results belong to #563; the remaining ABI controls retain #554/#551 and #567/#551 ownership. Constants and literal hashing controls MATCH in this run.','', 'To reproduce the permanent fixture check: `holbuild --maxheap 12000 build --tactic-timeout 600 foldedValueParityTheory`. The full corpus procedure forces targets listed by `python-o1-bytecode-fixtures`; exact progress, commands and exits are in `corpus/results.json`. Provision/export/execution/report helpers and the originally executed SML harness are retained in `runner/`. Scheduler handoff scripts record this run\'s process IDs and are historical records, not commands to replay. The corrected probe generator uses checked data equality for future runs.']
(dest/'REPORT.md').write_text('\n'.join(lines)+'\n')
print(json.dumps(report['verdict_counts']))
