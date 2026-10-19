"""Fail-fast prerequisite check for independent memory construction validation."""
from pathlib import Path
import subprocess

root = Path(__file__).resolve().parents[3]
pin = (root / 'VYPER_PIN').read_text().strip()
version = subprocess.check_output(['vyper', '--version'], text=True).strip()
print('Vyper:', version, flush=True)
if not version.endswith('commit.' + pin[:8]):
    raise RuntimeError(f'Expected pinned Vyper {pin}')
import eth.vm.forks.prague
import eth_abi
import eth_utils
print('PragueVM, eth_abi, eth_utils available', flush=True)
