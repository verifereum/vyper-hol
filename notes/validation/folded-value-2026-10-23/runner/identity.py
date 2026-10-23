from pathlib import Path
from importlib.metadata import version
import hashlib,json,subprocess
root=Path.cwd()
out=root/'.agent-files/folded-value-validation'
commands=[
 [out/'bootstrap/bin/uv','--version'],
 [out/'venv/bin/python','-I','-c','import sys,platform,vyper; print(platform.python_version()); print(vyper.__version__); print(vyper.__commit__); print(vyper.__file__)'],
 ['git','-C','/home/lukasz/vyper','rev-parse','HEAD'],
 ['git','-C','/home/lukasz/vyper','status','--porcelain','--untracked-files=all'],
 ['git','-C',out/'vyper-src','rev-parse','HEAD'],
 ['git','-C',out/'vyper-src','status','--porcelain','--untracked-files=all'],
 ['git','rev-parse','HEAD'],
 ['git','diff','--','frontend','lowering','semantics'],
 ['holbuild','--version'],
 [out/'bootstrap/bin/uv','pip','freeze','--python',out/'evm-venv/bin/python'],
]
rows=[]
for command in commands:
    result=subprocess.run(list(map(str,command)),capture_output=True,text=True)
    rows.append({'argv':list(map(str,command)),'exit':result.returncode,'stdout':result.stdout,'stderr':result.stderr})
(out/'identity.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps(rows[:4],indent=2))
