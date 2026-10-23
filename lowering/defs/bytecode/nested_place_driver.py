#!/usr/bin/env python3
"""Opt-in staged preparation/archive adapter. Never calls holbuild recursively."""
import argparse
import json
from pathlib import Path
import subprocess
import sys
import tarfile

HERE = Path(__file__).resolve().parent

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=['prepare', 'archive'])
    args = parser.parse_args()
    if args.mode == 'prepare':
        subprocess.run([sys.executable, str(HERE / 'memory_store_witnesses.py'),
                        'prepare', '--corpus', 'nested-places', '--repo', str(HERE.parents[2]),
                        '--fixtures', str(HERE / 'nested-places/oracle')], check=True)
        (HERE / 'nested-places/actual').mkdir(parents=True, exist_ok=True)
    else:
        # Only actual independently produced files are archived, including failures.
        # The HOL driver supplies statuses; presence of this archive is not MATCH.
        with tarfile.open(HERE / 'nested-places/validation.tar.gz', 'w:gz') as archive:
            for directory in ('oracle', 'actual'):
                root = HERE / 'nested-places' / directory
                for path in sorted(root.rglob('*')):
                    if path.is_file():
                        archive.add(path, arcname=str(path.relative_to(HERE / 'nested-places')))

if __name__ == '__main__':
    main()
