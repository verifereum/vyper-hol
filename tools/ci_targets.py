#!/usr/bin/env python3
"""Targets of the CI jobs that build part of the project, read from theory script headers."""

from __future__ import annotations

import argparse
import heapq
import os
import re
import statistics
import subprocess
import sys
import tomllib
from collections.abc import Iterable
from dataclasses import dataclass
from pathlib import Path

REPO = "verifereum/vyper-hol"
GENERATED_TESTS = Path("tests/generated")
TEST_COVERAGE_REPORT = Path("tests/vyperTestCoverageReportScript.sml")
WITNESS_ROLLUP = Path("lowering/evalCompilerWitnessesScript.sml")
WITNESS_TIMES = Path(".github/witness-times.txt")
WITNESS_LIB = "memoryStoreWitnessLib"
"""A theory that loads this library checks compiled fixtures against pinned Python output."""
FIXTURE = re.compile(rf"\b{WITNESS_LIB}\.evaluate\b")
WORKERS = 4
"""Theories one witness group builds at once: `holbuild -j"$(nproc)"` on a 4-vCPU runner."""

COMMENT = re.compile(r"\(\*.*?\*\)", re.DOTALL)
THEORY = re.compile(r"^Theory\s+([\w']+)", re.MULTILINE)
NAME = re.compile(r"[A-Za-z_][\w']*")
ATTRIBUTES = re.compile(r"\[[^]]*\]")
BUILT = re.compile(r"^\S+Z (\S+)Theory built in ([\d.]+)s$")


@dataclass(frozen=True)
class Header:
    """The `Theory`, `Ancestors` and `Libs` lines of a theory script."""

    name: str
    ancestors: tuple[str, ...]
    libs: tuple[str, ...]

    @classmethod
    def read(cls, script: Path) -> Header:
        """Parse the header of `script`.

        Raises:
            ValueError: `script` has no `Theory` line.
        """
        text = COMMENT.sub("", script.read_text())
        theory = THEORY.search(text)
        if theory is None:
            raise ValueError(f"{script} has no 'Theory <name>' line")
        # A section is its keyword line plus the indented lines after it; the
        # first other unindented line starts the theory body.
        sections: dict[str, list[str]] = {"Ancestors": [], "Libs": []}
        current: list[str] | None = None
        for line in text[theory.end():].splitlines()[1:]:
            words = line.split(maxsplit=1)
            if not words:
                continue
            if words[0] in sections:
                current = sections[words[0]]
                line = words[1] if len(words) > 1 else ""
            elif current is None or not line[0].isspace():
                break
            current += NAME.findall(ATTRIBUTES.sub("", line))
        return cls(theory[1], tuple(sections["Ancestors"]), tuple(sections["Libs"]))


class Project:
    """The project's theory scripts and SML libraries, by the name holbuild gives them."""

    def __init__(self, root: Path) -> None:
        self.root = root
        self.theories: dict[str, Path] = {}
        self.libs: set[str] = set()
        self.headers: dict[str, Header] = {}
        for directory, subdirs, files in os.walk(root):
            subdirs[:] = [d for d in subdirs if not d.startswith(".")]
            for file in files:
                if file.endswith("Script.sml"):
                    self.theories[file.removesuffix("Script.sml")] = Path(directory, file)
                elif file.endswith((".sml", ".sig")):
                    self.libs.add(file.rsplit(".", 1)[0])

    def header(self, theory: str) -> Header:
        """The header of the project's `theory`, read once."""
        if theory not in self.headers:
            self.headers[theory] = Header.read(self.theories[theory])
        return self.headers[theory]

    def roots(self) -> list[str]:
        """Theories of the build roots in holproject.toml."""
        return [Header.read(self.root / script).name for script in self.manifest()["build"]["roots"]]

    def dependency_roots(self) -> list[str]:
        """Targets of the dependency packages' build roots, which a build with no targets also builds.

        Raises:
            ValueError: holbuild has not fetched a dependency yet.
        """
        targets = []
        for name in self.manifest().get("dependencies", {}):
            manifest = self.root / ".holbuild" / "src" / name / "holproject.toml"
            if not manifest.is_file():
                raise ValueError(f"no {manifest}; run `holbuild buildhol` first")
            with open(manifest, "rb") as f:
                scripts = tomllib.load(f).get("build", {}).get("roots", [])
            targets += (f"{Path(script).name.removesuffix('Script.sml')}Theory" for script in scripts)
        return sorted(targets)

    def manifest(self) -> dict:
        """holproject.toml."""
        with open(self.root / "holproject.toml", "rb") as f:
            return tomllib.load(f)

    def ancestors(self, theories: Iterable[str]) -> set[str]:
        """`theories` and every project theory they descend from."""
        seen: set[str] = set()
        stack = [name for name in theories if name in self.theories]
        while stack:
            name = stack.pop()
            if name not in seen:
                seen.add(name)
                stack += (a for a in self.header(name).ancestors if a in self.theories)
        return seen

    def targets(self, theories: Iterable[str], libs: Iterable[str]) -> list[str]:
        """holbuild targets for the project's own `theories` and `libs`; HOL's are left out."""
        return sorted({f"{name}Theory" for name in theories if name in self.theories}
                      | {name for name in libs if name in self.libs})


def test_dependencies(project: Project) -> list[str]:
    """Project theories and libraries the generated tests and the coverage report load.

    Building these first lets the test groups start before the rest of the
    project is built; a test group then builds only its own test theories.
    """
    headers = [Header.read(script) for script in sorted(project.root.joinpath(GENERATED_TESTS).glob("*Script.sml"))]
    headers.append(Header.read(project.root / TEST_COVERAGE_REPORT))
    generated = {header.name for header in headers}
    return project.targets((name for header in headers for name in header.ancestors if name not in generated),
                           (name for header in headers for name in header.libs))


class Witnesses:
    """The witness theories only the witness rollup root reaches, which CI builds in parallel jobs."""

    def __init__(self, project: Project) -> None:
        self.project = project
        self.rollup = Header.read(project.root / WITNESS_ROLLUP).name
        others = project.ancestors(r for r in project.roots() if r != self.rollup)
        only_rollup = project.ancestors([self.rollup]) - others
        self.names = sorted(n for n in only_rollup if WITNESS_LIB in project.header(n).libs)
        self.deps = {n: [a for a in project.header(n).ancestors if a in self.names] for n in self.names}

    def fixtures(self, witness: str) -> int:
        """Fixture programs `witness` compiles: one `evaluate` call each."""
        return len(FIXTURE.findall(COMMENT.sub("", self.project.theories[witness].read_text())))

    def build_roots(self) -> list[str]:
        """Targets of every root but the witness rollup, the dependencies' roots included."""
        own = self.project.targets((r for r in self.project.roots() if r != self.rollup), ())
        return own + self.project.dependency_roots()

    def compiler(self) -> list[str]:
        """Project theories and libraries the witnesses load, other than witnesses."""
        headers = [self.project.header(n) for n in self.names]
        return self.project.targets((a for h in headers for a in h.ancestors if a not in self.names),
                                    (lib for h in headers for lib in h.libs))

    def units(self) -> list[list[str]]:
        """Witnesses that must share a group: each top witness with the witnesses it descends from."""
        unit_of = {n: {n} for n in self.names}
        for name, deps in self.deps.items():
            for dep in deps:
                merged = unit_of[name] | unit_of[dep]
                for member in merged:
                    unit_of[member] = merged
        units = {frozenset(u) for u in unit_of.values()}
        return sorted(sorted(u) for u in units)


class WitnessTimes:
    """Estimated build seconds of each witness, scaled from CI times by its fixture count.

    A times-file line is `<theory> <seconds> <fixtures>`: the median CI time
    and the fixtures the theory had then. A witness split or extended since
    keeps the per-fixture time; a witness the file doesn't name gets the
    median per-fixture time of those it does.
    """

    def __init__(self, measured: dict[str, tuple[float, int]], witnesses: Witnesses) -> None:
        if not measured:
            raise ValueError("witness times file names no witnesses; rerun tools/ci_targets.py witness-times")
        rates = {name: seconds / fixtures for name, (seconds, fixtures) in measured.items()}
        median = statistics.median(rates.values())
        self.deps = witnesses.deps
        self.seconds = {n: rates.get(n, median) * witnesses.fixtures(n) for n in witnesses.names}

    def makespan(self, theories: list[str]) -> float:
        """Seconds holbuild takes to build `theories` as one group.

        holbuild runs WORKERS theories at once and starts the first ready
        theory in target order; a theory is ready when its witness ancestors
        are built.
        """
        pending = list(theories)
        finished: dict[str, float] = {}
        running: list[tuple[float, str]] = []
        clock = 0.0
        while pending or running:
            ready = [n for n in pending if all(d in finished for d in self.deps[n])]
            for name in ready[:WORKERS - len(running)]:
                pending.remove(name)
                heapq.heappush(running, (clock + self.seconds[name], name))
            clock, name = heapq.heappop(running)
            finished[name] = clock
        return clock

    def plan(self, units: list[list[str]], groups: int) -> list[list[str]]:
        """Assign units to groups, longest first, each to the group it slows least.

        On a tie the unit goes to the group with the least work, so a long
        unit running alone does not leave its runner's other workers idle.
        """
        assigned: list[list[str]] = [[] for _ in range(groups)]
        for unit in sorted(units, key=lambda u: (-self.work(u), u)):
            def rank(group: list[str]) -> tuple[float, float]:
                return self.makespan(self.by_time(group + unit)), self.work(group)
            min(assigned, key=rank).extend(unit)
        return [self.by_time(group) for group in assigned]

    def work(self, theories: list[str]) -> float:
        """Total build seconds of `theories`."""
        return sum(self.seconds[n] for n in theories)

    def by_time(self, theories: list[str]) -> list[str]:
        """Theories longest first, the target order that lets holbuild start them first."""
        return sorted(theories, key=lambda n: (-self.seconds[n], n))


def read_witness_times(path: Path) -> dict[str, tuple[float, int]]:
    """Measured seconds and fixture count per witness (`<theory> <seconds> <fixtures>` lines, `#` comments)."""
    measured = {}
    for line in path.read_text().splitlines():
        if line and not line.startswith("#"):
            name, seconds, fixtures = line.split()
            measured[name] = (float(seconds), int(fixtures))
    return measured


def median_build_times(logs: Iterable[str], theories: Iterable[str]) -> dict[str, float]:
    """Median seconds of each of `theories` over its `<theory>Theory built in <n>s` log lines."""
    wanted = set(theories)
    samples: dict[str, list[float]] = {}
    for log in logs:
        for line in log.splitlines():
            match = BUILT.match(line.strip())
            if match and match[1] in wanted:
                samples.setdefault(match[1], []).append(float(match[2]))
    return {name: statistics.median(s) for name, s in samples.items()}


def format_witness_times(seconds: dict[str, float], witnesses: Witnesses) -> str:
    """The witness times file for the measured `seconds`, with today's fixture counts."""
    lines = ["# Median CI build seconds of each witness theory and its fixture count",
             "# then, written by `tools/ci_targets.py witness-times`. The witness",
             "# groups scale each time by the theory's fixture count now."]
    lines += [f"{name} {seconds[name]:.0f} {witnesses.fixtures(name)}" for name in sorted(seconds)]
    return "\n".join(lines) + "\n"


class CiLogs:
    """Logs of the jobs that built witnesses in successful holbuild.yml runs, read through `gh`."""

    def __init__(self, repo: str) -> None:
        self.repo = repo

    def recent_runs(self, limit: int) -> list[str]:
        """IDs of the latest successful runs."""
        return self.gh("run", "list", "-R", self.repo, "-w", "holbuild.yml", "-s", "success",
                       "-L", str(limit), "--json", "databaseId", "-q", ".[].databaseId").split()

    def witness_logs(self, run: str) -> list[str]:
        """Logs of the run's successful build and witness-group jobs."""
        jobs = self.gh("api", f"repos/{self.repo}/actions/runs/{run}/jobs", "--paginate", "-q",
                       '.jobs[]|select((.name=="build" or (.name|startswith("witnesses")))'
                       ' and .conclusion=="success")|.id')
        return [self.gh("api", f"repos/{self.repo}/actions/jobs/{job}/logs") for job in jobs.split()]

    def gh(self, *args: str) -> str:
        """Run `gh` and return its output."""
        return subprocess.run(["gh", *args], check=True, capture_output=True, text=True).stdout


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    commands.add_parser("test-deps", help="print what the test groups need besides their own theories")
    commands.add_parser("build-roots", help="print every build root but the witness rollup")
    commands.add_parser("compiler", help="print what the witnesses need besides other witnesses")
    group = commands.add_parser("witnesses", help="print the witnesses one witness group builds")
    group.add_argument("--group", type=int, required=True)
    group.add_argument("--groups", type=int, required=True)
    times = commands.add_parser("witness-times", help=f"rewrite {WITNESS_TIMES} from CI build times")
    times.add_argument("--runs", type=int, default=30, help="latest successful runs to read")
    args = parser.parse_args()

    project = Project(Path.cwd())
    if args.command == "test-deps":
        print(" ".join(test_dependencies(project)))
        return
    witnesses = Witnesses(project)
    if args.command == "build-roots":
        print(" ".join(witnesses.build_roots()))
    elif args.command == "compiler":
        print(" ".join(witnesses.compiler()))
    elif args.command == "witnesses":
        if not 0 <= args.group < args.groups:
            sys.exit(f"group {args.group} is not in 0 to {args.groups - 1}")
        estimate = WitnessTimes(read_witness_times(WITNESS_TIMES), witnesses)
        names = estimate.plan(witnesses.units(), args.groups)[args.group]
        # holbuild builds every root when given no targets.
        if not names:
            sys.exit(f"witness group {args.group} has no witnesses; use fewer groups")
        print(f"witness group {args.group}: about {estimate.makespan(names) / 60:.0f} min", file=sys.stderr)
        print(" ".join(f"{name}Theory" for name in names))
    else:
        ci = CiLogs(REPO)
        runs = ci.recent_runs(args.runs)
        seconds = median_build_times((log for run in runs for log in ci.witness_logs(run)), witnesses.names)
        WITNESS_TIMES.write_text(format_witness_times(seconds, witnesses))


if __name__ == "__main__":
    main()
