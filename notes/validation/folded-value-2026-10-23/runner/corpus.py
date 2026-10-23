from pathlib import Path
import json, re, subprocess, time
root=Path.cwd()
out=root/'.agent-files/folded-value-validation/corpus'
out.mkdir(exist_ok=True)
wrapper=(root/'lowering/defs/bytecode/python-o1-bytecode-fixtures').read_text()
targets=list(dict.fromkeys(re.findall(r'\bevalCompilerBytecode\w*Theory\b',wrapper)))
rows={}
for target in targets:
    command=['holbuild','--maxheap','12000','build','--force=theory','--tactic-timeout','600',target]
    start=time.time()
    with (out/(target+'.log')).open('w') as log:
        result=subprocess.run(command,stdout=log,stderr=subprocess.STDOUT)
    rows[target]={'argv':command,'exit':result.returncode,'seconds':round(time.time()-start,3)}
    (out/'results.json').write_text(json.dumps(rows,indent=2)+'\n')
    print(target,rows[target],flush=True)
