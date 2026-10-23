from pathlib import Path
import json,re,subprocess,time
root=Path.cwd()
out=root/'.agent-files/folded-value-validation'
expected=list(dict.fromkeys(re.findall(r'\bevalCompilerBytecode\w*Theory\b',(root/'lowering/defs/bytecode/python-o1-bytecode-fixtures').read_text())))
while True:
    rows=json.loads((out/'corpus/results.json').read_text())
    if all(name in rows for name in expected):break
    time.sleep(5)
# Keep actual holbuild exit statuses distinct from recorder timeout diagnostics.
for name,row in rows.items():
    if row['exit']==124 and 'batch_exit' in row:
        row['diagnostic_code']=124
        row['exit']=row['batch_exit']
    if name=='evalCompilerBytecodeAbiInternalCallsTheory' and 'argv' not in row:
        row['argv']=['holbuild','--maxheap','12000','-j3','build','--force=theory','--tactic-timeout','600','evalCompilerBytecodeAbiExternalDynamicTheory','evalCompilerBytecodeAbiEventsTheory','evalCompilerBytecodeAbiInternalCallsTheory']
(out/'corpus/results.json').write_text(json.dumps(rows,indent=2)+'\n')
steps=[]
for label,command in [
    ('prep-build',['holbuild','build','foldedValueValidationPrepTheory']),
    ('theorem-audit',['holbuild','--maxheap','12000','run','.folded_value_audit.sml']),
]:
    with (out/(label+'.log')).open('w') as log:
        result=subprocess.run(command,stdout=log,stderr=subprocess.STDOUT)
    steps.append({'step':label,'argv':command,'exit':result.returncode})
    (out/'finalize-status.json').write_text(json.dumps(steps,indent=2)+'\n')
    print(label,result.returncode,flush=True)
    if result.returncode:raise SystemExit(result.returncode)
result=subprocess.run(['python3','-I',str(out/'report.py')])
if result.returncode:raise SystemExit(result.returncode)
result=subprocess.run(['python3','-I',str(out/'verify_bundle.py')])
raise SystemExit(result.returncode)
