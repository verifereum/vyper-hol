#!/usr/bin/env python3
"""Reproduce the event oracle with an isolated, pinned Python Vyper install.

The supplied environment must contain Python 3.11.11 and the dependencies in
python-o1-oracle-constraints.txt. No HOL output is an input to this generator.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile


def run(argv, **kwargs):
    return subprocess.run(argv, check=True, text=True, capture_output=True, **kwargs)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--python", type=Path, required=True)
    parser.add_argument("--vyper-repo", type=Path, required=True)
    parser.add_argument("--update", action="store_true")
    args = parser.parse_args()
    base = Path(__file__).resolve().parent
    repo = base.parents[0]
    pin = (repo / "VYPER_PIN").read_text().strip()
    compiler = args.vyper_repo.resolve()
    actual = run(["git", "-C", str(compiler), "rev-parse", "HEAD"]).stdout.strip()
    if actual != pin or run([
        "git", "-C", str(compiler), "status", "--porcelain", "--untracked-files=all"
    ]).stdout:
        raise RuntimeError("Vyper source checkout must be clean and match VYPER_PIN")
    # Preserve the venv path: resolving its Python symlink loses the install root.
    python = args.python.absolute()
    install_root = python.parent.parent
    env = {k: v for k, v in os.environ.items()
           if k not in ("PYTHONPATH", "PYTHONHOME", "PYTHONSTARTUP")}
    installed = Path(run([
        str(python), "-I", "-c",
        "import vyper; from pathlib import Path; print(Path(vyper.__file__).resolve().parent)"
    ], env=env).stdout.strip())
    if install_root.resolve() not in installed.parents:
        raise RuntimeError("Vyper was imported outside the isolated environment")
    # Verify installed compiler source, including builtin interfaces, against
    # the clean pinned checkout, rather than trusting only a version string.
    compiler_sources = {}
    tracked = run(["git", "-C", str(compiler), "ls-files", "-z", "vyper"]).stdout.split("\0")
    for name in tracked:
        source = compiler / name
        if not name or source.suffix not in (".py", ".vyi"):
            continue
        packaged = installed / Path(name).relative_to("vyper")
        if not packaged.exists() or packaged.read_bytes() != source.read_bytes():
            raise RuntimeError(f"installed compiler source differs from VYPER_PIN: {name}")
        compiler_sources[name] = hashlib.sha256(source.read_bytes()).hexdigest()
    dependencies = json.loads(run([
        str(python), "-I", "-c",
        "import json; from importlib.metadata import version; "
        "print(json.dumps({k: version(k) for k in "
        "['cbor2','immutables','lark','packaging','pycryptodome','wheel']}))"
    ], env=env).stdout)
    for name, version in dependencies.items():
        if f"{name}=={version}" not in (
            base / "python-o1-oracle-constraints.txt"
        ).read_text().splitlines():
            raise RuntimeError(f"unexpected dependency: {name}=={version}")
    stems = (base / "event-fixtures.txt").read_text().splitlines()
    if len(stems) != len(set(stems)) or any(not s.startswith("event_") for s in stems):
        raise RuntimeError("invalid event fixture manifest")
    with tempfile.TemporaryDirectory(prefix="event-oracle-") as temp:
        stage = Path(temp)
        sources = stage / "sources"
        sources.mkdir()
        for stem in stems:
            shutil.copyfile(base / "python-event-no-asm-opt-sources" / f"{stem}.vy",
                            sources / f"{stem}.vy")
        output = stage / "oracle"
        run([
            str(python), "-I", str(base / "python_o1_bytecode_oracle.py"),
            "--expected-commit", pin, "--expected-python", "3.11.11",
            "--generator-uv", "preprovisioned environment (no uv invocation)",
            "--expected-install-root", str(install_root),
            "--sources", str(sources), "--fixture-manifest", str(base / "event-fixtures.txt"),
            "--output", str(output)
        ], env=env)
        ast_dir = stage / "ast"
        ast_dir.mkdir()
        checker_stems = (base / "event-checker-fixtures.txt").read_text().splitlines()
        for stem in checker_stems + ["libp"]:
            shutil.copyfile(base / "python-event-no-asm-opt-sources" / f"{stem}.vy",
                            sources / f"{stem}.vy")
        for stem in stems + checker_stems:
            # Compile with relative paths so the exported AST is reproducible.
            result = run([
                str(python), "-I", "-m", "vyper", "--experimental-codegen",
                "--evm-version", "prague", "-O", "none",
                "--disable-bytecode-metadata", "-f", "annotated_ast,layout",
                f"{stem}.vy"
            ], cwd=sources, env=env)
            raw = stage / f"{stem}.jsonl"
            raw.write_text(result.stdout)
            run([str(python), "-I", str(repo / "tests/sanitize_check_contract_json.py"),
                 str(raw), str(ast_dir / f"{stem}.json"),
                 "--replace", f"{sources}/=",
                 "--replace", f"{install_root}/=pinned-vyper/"])
        provenance = json.loads((output / "provenance.json").read_text())
        provenance["verified_compiler_sources_sha256"] = hashlib.sha256(
            json.dumps(compiler_sources, sort_keys=True).encode()).hexdigest()
        provenance["verified_compiler_source_count"] = len(compiler_sources)
        provenance["generator_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
        provenance["bytecode_generator_sha256"] = hashlib.sha256(
            (base / "python_o1_bytecode_oracle.py").read_bytes()).hexdigest()
        provenance["sanitizer_sha256"] = hashlib.sha256(
            (repo / "tests/sanitize_check_contract_json.py").read_bytes()).hexdigest()
        for stem in stems:
            provenance["fixtures"][stem]["source"] = f"python-event-no-asm-opt-sources/{stem}.vy"
            provenance["fixtures"][stem]["annotated_ast_layout_sha256"] = hashlib.sha256(
                (ast_dir / f"{stem}.json").read_bytes()).hexdigest()
        provenance["checker_only"] = {
            stem: {
                "source": f"python-event-no-asm-opt-sources/{stem}.vy",
                "source_sha256": hashlib.sha256((sources / f"{stem}.vy").read_bytes()).hexdigest(),
                "annotated_ast_layout_sha256": hashlib.sha256(
                    (ast_dir / f"{stem}.json").read_bytes()).hexdigest()
            } for stem in checker_stems
        }
        provenance["checker_import_sources"] = {
            "libp.vy": hashlib.sha256((sources / "libp.vy").read_bytes()).hexdigest()
        }
        (output / "provenance.json").write_text(
            json.dumps(provenance, indent=2, sort_keys=True) + "\n")
        log = [f"VYPER_PIN {pin}", "Python 3.11.11; isolated import root verified",
               "Clean Vyper checkout and exact runtime dependency versions verified",
               "Prague; OptimizationLevel.NONE; experimental codegen; no metadata"]
        for stem in stems:
            entry = provenance["fixtures"][stem]
            log.append(f"{stem}: deploy_sha256={entry['deploy_sha256']} "
                       f"runtime_sha256={entry['runtime_sha256']} "
                       f"ast_layout_sha256={entry['annotated_ast_layout_sha256']}")
        for stem in checker_stems:
            log.append(f"{stem}: checker-only ast_layout_sha256="
                       f"{provenance['checker_only'][stem]['annotated_ast_layout_sha256']}")
        (output / "generation.log").write_text("\n".join(log) + "\n")
        destinations = [(output, base / "python-event-no-asm-opt"),
                        (ast_dir, repo / "tests/fixtures/check_contract/events")]
        for generated, destination in destinations:
            if args.update:
                destination.mkdir(parents=True, exist_ok=True)
            expected = {p.name for p in generated.iterdir()}
            if destination.exists() and {p.name for p in destination.iterdir()} - expected:
                raise RuntimeError(f"unexpected files in {destination}")
            for source in generated.iterdir():
                target = destination / source.name
                if args.update:
                    shutil.copyfile(source, target)
                elif not target.exists() or source.read_bytes() != target.read_bytes():
                    raise RuntimeError(f"stale or missing event fixture: {target}")
        print(f"{'Updated' if args.update else 'Reproduced'} {len(stems)} pinned event "
              f"deploy/runtime oracle pairs and {len(stems) + len(checker_stems)} sanitized AST/layout inputs")


if __name__ == "__main__":
    main()
