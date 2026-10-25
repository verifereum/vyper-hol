#!/usr/bin/env python3
"""Export pinned upstream tests and verify their compiler-profile provenance."""

from __future__ import annotations

import argparse
import hashlib
import importlib.metadata
import json
import os
import platform
import shutil
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def portable_paths(value: Any, prefixes: dict[str, str]) -> Any:
    """Remove checkout/output roots from exported paths, including object keys."""
    if isinstance(value, str):
        for prefix, replacement in prefixes.items():
            if value.startswith(prefix):
                return replacement + value[len(prefix):]
        return value
    if isinstance(value, list):
        return [portable_paths(item, prefixes) for item in value]
    if isinstance(value, dict):
        return {
            portable_paths(key, prefixes): portable_paths(item, prefixes)
            for key, item in value.items()
        }
    return value


@dataclass(frozen=True)
class Exports:
    repo: Path

    @property
    def profile(self) -> dict[str, Any]:
        return json.loads((self.repo / "tests/semantics-profile.json").read_text())

    def inputs(self) -> dict[str, str]:
        return {
            name: digest(self.repo / name)
            for name in (
                "VYPER_PIN", "tests/semantics-profile.json",
                "tests/semantics-test-constraints.txt", "tests/semantics-build-constraints.txt",
                "tools/vyper_test_exports.py",
                ".github/actions/setup-vyper-test-exports/action.yml",
            )
        }

    def cache_key(self) -> str:
        return hashlib.sha256(json.dumps(self.inputs(), sort_keys=True).encode()).hexdigest()

    def settings(self, path: Path) -> list[dict[str, Any]]:
        # Resolved settings belong to each deployment, not to the whole run:
        # upstream tests override optimisation, backend and source pragmas.
        settings: list[dict[str, Any]] = []
        for name, item in json.loads(path.read_text()).items():
            for index, trace in enumerate(item["traces"]):
                if trace["trace_type"] == "deployment":
                    settings.append({
                        "item": name, "trace": index,
                        "deployment_type": trace["deployment_type"],
                        "compiler_settings": trace["compiler_settings"],
                    })
        return settings

    def check(self, path: Path) -> None:
        sidecar = Path(str(path) + ".provenance")
        if not sidecar.is_file():
            raise ValueError(f"missing {sidecar}; regenerate with tools/vyper_test_exports.py")
        recorded = json.loads(sidecar.read_text())
        for key, expected in (
            ("schema_version", 1), ("inputs", self.inputs()),
            ("export_sha256", digest(path)), ("resolved_settings", self.settings(path)),
            ("profile", self.profile),
        ):
            if recorded.get(key) != expected:
                raise ValueError(f"stale {path}: provenance {key} differs; regenerate exports")
        for source, expected in recorded["fixture_sources"].items():
            if digest(self.repo / source) != expected:
                raise ValueError(f"stale {path}: fixture source {source} differs")

    def generate(self, args: argparse.Namespace) -> None:
        profile = self.profile
        if platform.python_version() != profile["python_version"]:
            raise ValueError(f"Python {platform.python_version()}, expected {profile['python_version']}")
        pin = (self.repo / "VYPER_PIN").read_text().strip()
        actual = subprocess.check_output(
            ["git", "-C", str(args.vyper_repo), "rev-parse", "HEAD"], text=True
        ).strip()
        if actual != pin:
            raise ValueError(f"Vyper checkout {actual}, expected {pin}")
        dirty = subprocess.check_output(
            ["git", "-C", str(args.vyper_repo), "status", "--porcelain"], text=True
        )
        if dirty:
            raise ValueError("Vyper checkout is dirty; refusing mixed-source exports")
        for line in (self.repo / "tests/semantics-test-constraints.txt").read_text().splitlines():
            if not line or line.startswith("#"):
                continue
            package, expected = line.split("==")
            actual = importlib.metadata.version(package)
            if actual != expected:
                raise ValueError(f"{package} {actual}, expected {expected}")
        if importlib.metadata.version("vyper") != profile["vyper_version"]:
            raise ValueError(f"expected Vyper package {profile['vyper_version']}")
        output = args.output.resolve()
        if output.exists():
            raise ValueError(f"output already exists: {output}; use a fresh export directory")
        fixture_root = args.vyper_repo / "tests/hol_fixtures"
        if args.fixture and fixture_root.exists():
            raise ValueError(f"temporary fixture directory already exists: {fixture_root}")
        fixture_sources = {}
        selections = list(args.test) if args.test or args.fixture else ["tests/functional"]
        if any(not test.startswith("tests/") for test in selections):
            raise ValueError("test selections must be paths below tests/")
        try:
            for source in args.fixture:
                source = source.resolve()
                relative = source.relative_to(self.repo).as_posix()
                fixture_sources[relative] = digest(source)
                target = fixture_root / source.parent.name / source.name
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(source, target)
                selections.append(target.relative_to(args.vyper_repo).as_posix())
            command = [
                sys.executable, "-m", "pytest", "-s", "-n0", "--export", str(output),
                *profile["pytest_args"], "-m", "not fuzzing", *selections,
            ]
            env = dict(os.environ)
            for variable in ("PYTEST_ADDOPTS", "PYTEST_PLUGINS", "PYTHONPATH", "PYTHONHOME"):
                env.pop(variable, None)
            subprocess.run(command, cwd=args.vyper_repo, env=env, check=True)
        finally:
            if fixture_sources:
                shutil.rmtree(fixture_root)
        files = sorted(output.rglob("*.json"))
        if not files:
            raise ValueError(f"no exports produced in {output}")
        for path in files:
            data = portable_paths(json.loads(path.read_text()), {
                str(output) + "/": "vyper-test-exports/",
                str(args.vyper_repo) + "/": "",
            })
            path.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")
            provenance = {
                "schema_version": 1, "inputs": self.inputs(), "profile": profile,
                "export_sha256": digest(path), "test_selections": selections,
                "fixture_sources": fixture_sources, "resolved_settings": self.settings(path),
            }
            Path(str(path) + ".provenance").write_text(
                json.dumps(provenance, indent=2, sort_keys=True) + "\n"
            )
            self.check(path)
        print(f"exported and verified {len(files)} files")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    commands.add_parser("cache-key")
    generate = commands.add_parser("generate")
    generate.add_argument("--vyper-repo", type=Path, required=True)
    generate.add_argument("--output", type=Path, required=True)
    generate.add_argument("--test", action="append", default=[])
    generate.add_argument("--fixture", type=Path, action="append", default=[])
    check = commands.add_parser("check")
    check.add_argument("paths", type=Path, nargs="+")
    args = parser.parse_args()
    exports = Exports(Path(__file__).resolve().parents[1])
    if args.command == "cache-key":
        print(exports.cache_key())
    elif args.command == "generate":
        args.vyper_repo = args.vyper_repo.resolve()
        exports.generate(args)
    else:
        for path in args.paths:
            files = sorted(path.rglob("*.json")) if path.is_dir() else [path]
            if not files:
                raise ValueError(f"no exports in {path}")
            for file in files:
                exports.check(file)


if __name__ == "__main__":
    main()
