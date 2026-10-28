#!/usr/bin/env python3
"""Opt-in staged preparation/archive adapter. Never calls holbuild recursively."""
import argparse
import json
from pathlib import Path
import subprocess
import sys
import tarfile

HERE = Path(__file__).resolve().parent

def archive_selected(corpus, output, names, manifest=None):
    with tarfile.open(corpus / output, 'w:gz') as archive:
        for name in names:
            for directory in ('sources', 'oracle', 'actual'):
                for path in sorted((corpus / directory).glob(name+'.*')):
                    if path.is_file():
                        archive.add(path, arcname=str(path.relative_to(corpus)))
        archive.add(corpus / 'oracle/provenance.json', arcname='oracle/provenance.json')
        if manifest is not None:
            archive.add(corpus / manifest, arcname=manifest)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=['prepare', 'archive', 'execute', 'matrix-prepare', 'matrix-archive', 'diagnostic-archive', 'trace-prepare', 'witness-archive'])
    parser.add_argument('--case')
    args = parser.parse_args()
    if args.mode == 'trace-prepare':
        corpus = HERE / 'nested-places'
        with tarfile.open(corpus / 'diagnostic.tar.gz') as archive:
            archive.extractall(corpus, filter='data')
    elif args.mode == 'matrix-prepare':
        from nested_place_cases import CONDITIONAL
        import memory_store_witnesses as witnesses
        corpus = HERE / 'nested-places'
        (corpus / 'actual').mkdir(parents=True, exist_ok=True)
        witnesses.prepare(HERE.parents[2], corpus, corpus / 'oracle', check=False)
        names = sorted(path.stem for path in (corpus / 'sources').glob('*.vy'))
        (corpus / 'matrix.txt').write_text('\n'.join(names) + '\n')
        (corpus / 'actual/conditional.json').write_text(json.dumps(CONDITIONAL, indent=2)+'\n')
    elif args.mode == 'diagnostic-archive':
        corpus = HERE / 'nested-places'
        names = (corpus / 'diagnostic.txt').read_text().splitlines()
        archive_selected(corpus, 'diagnostic.tar.gz', names, 'diagnostic.txt')
    elif args.mode == 'witness-archive':
        if not args.case or Path(args.case).name != args.case:
            parser.error('witness-archive requires a source stem in --case')
        archive_selected(HERE / 'nested-places', args.case+'-validation.tar.gz', [args.case])
    elif args.mode == 'matrix-archive':
        corpus = HERE / 'nested-places'
        summary = {}
        for path in sorted((corpus / 'actual').glob('*.stages')):
            summary[path.stem] = path.read_text().splitlines()
        (corpus / 'actual/status.json').write_text(json.dumps(summary, indent=2)+'\n')
        with tarfile.open(corpus / 'matrix.tar.gz', 'w:gz') as archive:
            for directory in ('sources', 'oracle', 'actual'):
                for path in sorted((corpus / directory).rglob('*')):
                    if path.is_file():
                        archive.add(path, arcname=str(path.relative_to(corpus)))
            archive.add(corpus / 'matrix.txt', arcname='matrix.txt')
    elif args.mode == 'prepare':
        subprocess.run([sys.executable, str(HERE / 'memory_store_witnesses.py'),
                        'prepare', '--corpus', 'nested-places', '--repo', str(HERE.parents[2]),
                        '--fixtures', str(HERE / 'nested-places/oracle')], check=True)
        (HERE / 'nested-places/actual').mkdir(parents=True, exist_ok=True)
    elif args.mode == 'execute':
        with tarfile.open(HERE / 'nested-places/validation.tar.gz') as archive:
            archive.extractall(HERE / 'nested-places', filter='data')
        from nested_place_execute import execute
        try:
            execute()
        except Exception as error:
            (HERE / 'nested-places/behaviour-status.json').write_text(
                json.dumps({'status': 'ERROR', 'error': f'{type(error).__name__}: {error}'}) + '\n')
            raise
        else:
            (HERE / 'nested-places/behaviour-status.json').write_text('{"status":"PASS"}\n')
        finally:
            import shutil
            report = HERE / 'nested-places/actual/behaviour.json'
            if report.exists():
                shutil.copyfile(report, HERE / 'nested-places/behaviour.json')
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
