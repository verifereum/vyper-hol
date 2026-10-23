from pathlib import Path
import os, subprocess, json, time

root = Path.cwd()
out = root / '.agent-files/folded-value-validation'
uv = out / 'bootstrap/bin/uv'
env = dict(os.environ)
for key in ('PYTHONPATH', 'PYTHONHOME', 'PYTHONSTARTUP'):
    env.pop(key, None)
env.update(UV_PYTHON_INSTALL_DIR=str(out / 'python'),
           UV_CONSTRAINT=str(root / 'lowering/defs/bytecode/python-o1-oracle-constraints.txt'),
           UV_BUILD_CONSTRAINT=str(root / 'lowering/defs/bytecode/python-o1-oracle-constraints.txt'),
           SETUPTOOLS_SCM_PRETEND_VERSION_FOR_VYPER='0.5.0a4+cd74ce4f')
commands = [
    ['git', 'clone', '--quiet', '--no-checkout', '--no-local', '/home/lukasz/vyper', str(out / 'vyper-src')],
    ['git', '-c', 'advice.detachedHead=false', '-C', str(out / 'vyper-src'), 'checkout', '--quiet', '--detach', (root / 'VYPER_PIN').read_text().strip()],
    [str(uv), 'venv', '--managed-python', '--python', '3.11.11', str(out / 'venv')],
    [str(uv), 'pip', 'install', '--python', str(out / 'venv/bin/python'), str(out / 'vyper-src')],
]
with (out / 'provision.log').open('w') as log:
    for command in commands:
        log.write(json.dumps(command) + '\n'); log.flush()
        result = subprocess.run(command, env=env, stdout=log, stderr=subprocess.STDOUT)
        log.write('EXIT=' + str(result.returncode) + '\n'); log.flush()
        if result.returncode:
            raise SystemExit(result.returncode)
print('Pinned compiler environment provisioned:', out / 'venv')
