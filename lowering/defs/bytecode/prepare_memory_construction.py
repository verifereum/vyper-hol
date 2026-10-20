"""Run oracle preparation with the pinned compiler's own interpreter."""
from pathlib import Path
import argparse
import shutil
import subprocess

here = Path(__file__).resolve().parent
repo = here.parents[2]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--fixtures', type=Path, default=here / 'memory-stores/oracle')
parser.add_argument('--check', action='store_true')
args = parser.parse_args()
vyper = Path(shutil.which('vyper')).resolve()
python = vyper.read_text().splitlines()[0].removeprefix('#!')
print('Pinned compiler environment:', python, flush=True)
subprocess.run([python, str(here / 'memory_store_witnesses.py'), 'prepare',
                '--repo', str(repo), '--fixtures', str(args.fixtures.resolve())]
               + (['--check'] if args.check else []), check=True, cwd=repo)
