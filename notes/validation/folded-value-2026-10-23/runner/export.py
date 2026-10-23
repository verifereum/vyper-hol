from pathlib import Path
import hashlib, json, os, shutil, subprocess

root = Path.cwd()
out = root / '.agent-files/folded-value-validation'
b = root / 'lowering/defs/bytecode'
python = out / 'venv/bin/python'
env = dict(os.environ)
for key in ('PYTHONPATH', 'PYTHONHOME', 'PYTHONSTARTUP'):
    env.pop(key, None)
for name in ('sources', 'ast', 'oracle', 'logs', 'single'):
    (out / name).mkdir(exist_ok=True)
def run(label, command):
    result = subprocess.run(list(map(str,command)), env=env, capture_output=True)
    (out / 'logs' / (label + '.stdout')).write_bytes(result.stdout)
    (out / 'logs' / (label + '.stderr')).write_bytes(result.stderr)
    (out / 'logs' / (label + '.command.json')).write_text(json.dumps({'argv':list(map(str,command)), 'exit':result.returncode},indent=2)+'\n')
    return result
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
rows = {}
stems = (b / 'folded-value-witnesses.txt').read_text().split()
for stem in stems:
    source = out / 'sources' / (stem + '.vy')
    shutil.copyfile(b / 'folded-value-sources' / source.name,source)
    raw = out / 'ast' / (stem + '.jsonl')
    ast = run(stem+'.ast',[out/'venv/bin/vyper','-f','annotated_ast,layout',source])
    raw.write_bytes(ast.stdout)
    row = {'source_sha256':sha(source), 'python_ast_exit':ast.returncode}
    if ast.returncode == 0:
        sanitized = out / 'ast' / (stem + '.json')
        result = run(stem+'.sanitize',[python,'-I',root/'tests/sanitize_check_contract_json.py',raw,sanitized,'--replace',str(out)+'=folded-value-validation','--replace',str(root)+'=.'])
        if result.returncode == 0:
            row['ast_sha256']=sha(sanitized)
            shutil.copyfile(sanitized,out/'oracle'/sanitized.name)
    if stem != 'method_id_var':
        single = out / 'single' / stem
        single.mkdir(exist_ok=True)
        shutil.copyfile(source,single/source.name)
        manifest = single/'manifest.txt'
        manifest.write_text(stem+'\n')
        result = run(stem+'.oracle',[python,'-I',b/'python_o1_bytecode_oracle.py','--expected-commit',(root/'VYPER_PIN').read_text().strip(),'--expected-python','3.11.11','--generator-uv','0.10.11','--expected-install-root',out/'venv','--sources',single,'--fixture-manifest',manifest,'--output',single/'generated'])
        row['python_bytecode_exit']=result.returncode
        if result.returncode == 0:
            oracle = single/'generated'/(stem+'.hex')
            shutil.copyfile(oracle,out/'oracle'/oracle.name)
            row['oracle_sha256']=sha(oracle)
    rows[stem]=row
    (out/'exports.json').write_text(json.dumps(rows,indent=2)+'\n')
    print(stem,json.dumps(row),flush=True)
metadata = json.loads(next((out/'single').glob('*/generated/provenance.json')).read_text())
metadata['fixtures']={}
for stem,row in rows.items():
    if row.get('python_bytecode_exit') == 0:
        item=json.loads((out/'single'/stem/'generated/provenance.json').read_text())['fixtures'][stem]
        item['source']='folded-value-sources/'+stem+'.vy'
        metadata['fixtures'][stem]=item
metadata['source_checkout']='/home/lukasz/vyper'
metadata['source_revision']=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
metadata['dirty_diff_sha256']=hashlib.sha256(subprocess.check_output(['git','diff'])).hexdigest()
metadata['generator_note']='Per-witness invocations of python_o1_bytecode_oracle.py; source labels corrected from its hardcoded baseline directory. Original provenance and command logs retained in single/ and logs/.'
(out/'oracle/provenance.json').write_text(json.dumps(metadata,indent=2,sort_keys=True)+'\n')
