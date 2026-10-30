#!/usr/bin/env python3
"""Assign the generated Vyper test theories to CI test groups by build time."""

from __future__ import annotations

import argparse
import heapq
import re
import statistics
import subprocess
import sys
from collections.abc import Iterable
from dataclasses import dataclass
from pathlib import Path

REPO = "verifereum/vyper-hol"
GROUPS_FILE = Path(".github/vyper-test-groups.txt")
GENERATED = Path("tests/generated")
WORKERS = 1
"""Conservative CI concurrency: one worker below 12 GiB, at most two otherwise."""

BUILT = re.compile(r"^\S+Z (vyperTest(?:Defs)?_\S+)Theory built in ([\d.]+)s$")
ANCESTOR = re.compile(r"^Ancestors (vyperTestDefs_\S+)$", re.MULTILINE)
CHUNK = re.compile(r"^(.*)_chunk\d+$")
PART = re.compile(r"^(.*)_part\d+$")


@dataclass(frozen=True)
class Test:
    """A generated test theory and the definitions theory it replays traces from."""

    name: str
    defs: str


def generated_tests(generated: Path) -> list[Test]:
    """Read the test theories in `generated`, in name order."""
    tests = []
    for script in sorted(generated.glob("vyperTest_*Script.sml")):
        match = ANCESTOR.search(script.read_text())
        if match is None:
            raise ValueError(f"{script} has no 'Ancestors vyperTestDefs_...' line")
        tests.append(Test(script.name.removesuffix("Script.sml"), match[1]))
    return tests


class BuildTimes:
    """Median build seconds per theory, from `<theory>Theory built in <n>s` log lines."""

    def __init__(self, logs: Iterable[str], tests: list[Test], workers: int = WORKERS) -> None:
        if workers < 1:
            raise ValueError("workers must be positive")
        self.workers = workers
        samples: dict[str, list[float]] = {}
        for log in logs:
            for line in log.splitlines():
                match = BUILT.match(line.strip())
                if match:
                    samples.setdefault(match[1], []).append(float(match[2]))
        self.seconds = {name: statistics.median(s) for name, s in samples.items()}
        self.estimate_new_parts(tests)
        self.estimate_new_chunks(tests)

    def estimate_new_parts(self, tests: list[Test]) -> None:
        """Estimate independent replay AND definitions parts from whole-file times.

        Part zero keeps the unsuffixed name. Until any suffixed part has a
        measurement, divide the old whole-file time among all parts, including
        zero. Once siblings have measurements, keep them (and part zero) intact
        and use their median for missing siblings. These equal-share estimates
        are only a bootstrap; fresh partitioned CI measurements should replace them.
        """
        families: dict[str, set[str]] = {}
        names = {name for test in tests for name in (test.name, test.defs)}
        for name in sorted(names):
            match = PART.match(name)
            if match:
                families.setdefault(match[1], set()).add(name)
        for whole, siblings in families.items():
            family = siblings | ({whole} & names)
            measured = [self.seconds[name] for name in sorted(family) if name in self.seconds]
            if any(name in self.seconds for name in siblings):
                estimate = statistics.median(measured)
                for name in family:
                    self.seconds.setdefault(name, estimate)
            elif whole in self.seconds:
                estimate = self.seconds[whole] / len(family)
                for name in family:
                    self.seconds[name] = estimate

    def estimate_new_chunks(self, tests: list[Test]) -> None:
        """Give chunks no log built yet an equal share of their unsplit test's time.

        A test split into trace chunks has CI times only for the unsplit
        test until the chunks have run. The first chunk keeps the unsplit
        name. Treat that timing as unsplit only while no suffixed chunk has
        a measurement; otherwise preserve all measured chunk timings.
        """
        chunks: dict[str, set[str]] = {}
        for test in tests:
            for name in (test.name, test.defs):
                match = CHUNK.match(name)
                if match:
                    chunks.setdefault(match[1], set()).add(name)
        current = {name for test in tests for name in (test.name, test.defs)}
        for whole, names in chunks.items():
            if whole in self.seconds:
                unsplit = not any(name in self.seconds for name in names)
                if whole in current:
                    names.add(whole)
                estimate = self.seconds[whole] / len(names)
                if unsplit and whole in names:
                    self.seconds[whole] = estimate
                for name in names:
                    self.seconds.setdefault(name, estimate)

    def missing(self, tests: Iterable[Test]) -> list[str]:
        """Theories of `tests` that no log built."""
        names = {name for test in tests for name in (test.name, test.defs)}
        return sorted(names - self.seconds.keys())

    def cost(self, test: Test) -> float:
        """Seconds to build a test with its definitions theory, one after the other."""
        return self.seconds[test.defs] + self.seconds[test.name]

    def makespan(self, tests: list[Test]) -> float:
        """Seconds holbuild takes to build `tests` as one group.

        holbuild runs `self.workers` theories at once and starts the first ready
        theory in target order, a definitions theory before its tests. Tests
        sharing a definitions theory build it once.
        """
        pending: list[tuple[str, str | None]] = []
        for test in tests:
            if all(name != test.defs for name, _ in pending):
                pending.append((test.defs, None))
            pending.append((test.name, test.defs))
        finished: dict[str, float] = {}
        running: list[tuple[float, str]] = []
        clock = 0.0
        while pending or running:
            ready = [job for job in pending if job[1] is None or job[1] in finished]
            for job in ready[:self.workers - len(running)]:
                pending.remove(job)
                heapq.heappush(running, (clock + self.seconds[job[0]], job[0]))
            clock, name = heapq.heappop(running)
            finished[name] = clock
        return clock

    def plan(self, tests: list[Test], groups: int) -> list[list[Test]]:
        """Assign tests to groups, longest first, each to the group it slows least.

        A test goes to the group whose build ends earliest with it; on a tie,
        to the group with the least work, so a long test running alone does
        not leave its runner's other workers idle while another group queues.
        Trace chunks sharing definitions and independent parts of one file
        go to different groups while there are groups left, so their replays
        run in parallel without introducing sibling dependencies.
        """
        if groups < 1:
            raise ValueError("groups must be positive")
        assigned: list[list[Test]] = [[] for _ in range(groups)]
        for test in self.by_cost(tests):
            family = PART.sub(r"\1", test.defs)
            apart = [group for group in assigned
                     if all(PART.sub(r"\1", other.defs) != family for other in group)] or assigned
            def rank(group: list[Test]) -> tuple[float, float]:
                return self.makespan(self.by_cost(group + [test])), sum(map(self.cost, group))
            min(apart, key=rank).append(test)
        return [self.by_cost(group) for group in assigned]

    def by_cost(self, tests: list[Test]) -> list[Test]:
        """Tests longest first, the target order that lets holbuild start them first."""
        return sorted(tests, key=lambda test: (-self.cost(test), test.name))


class CiLogs:
    """Test-group job logs of successful holbuild.yml runs, read through `gh`."""

    def __init__(self, repo: str) -> None:
        self.repo = repo

    def recent_runs(self, limit: int) -> list[str]:
        """IDs of the latest successful runs."""
        return self.gh("run", "list", "-R", self.repo, "-w", "holbuild.yml", "-s", "success",
                       "-L", str(limit), "--json", "databaseId", "-q", ".[].databaseId").split()

    def test_logs(self, run: str) -> list[str]:
        """Logs of the run's successful test-group jobs."""
        jobs = self.gh("api", f"repos/{self.repo}/actions/runs/{run}/jobs", "--paginate", "-q",
                       '.jobs[]|select((.name|startswith("vyper-tests")) and .conclusion=="success")|.id')
        return [self.gh("api", "--allow-escape-sequences", f"repos/{self.repo}/actions/jobs/{job}/logs")
                for job in jobs.split()]

    def gh(self, *args: str) -> str:
        """Run `gh` and return its output."""
        return subprocess.run(["gh", *args], check=True, capture_output=True, text=True).stdout


def read_groups(path: Path) -> dict[str, int]:
    """Group of each test theory in a groups file (`<group> <theory>` lines, `#` comments)."""
    groups = {}
    for line in path.read_text().splitlines():
        if line and not line.startswith("#"):
            group, name = line.split()
            groups[name] = int(group)
    return groups


def group_targets(tests: list[Test], groups_file: dict[str, int], group: int, groups: int) -> list[str]:
    """Theories test group `group` builds, in groups-file order.

    Tests the groups file doesn't name (added since it was written) are dealt
    out over the groups in name order; names of removed tests are ignored.
    """
    if not 0 <= group < groups:
        raise ValueError(f"group {group} is not in 0 to {groups - 1}")
    outside = sorted({g for g in groups_file.values() if not 0 <= g < groups})
    if outside:
        raise ValueError(f"groups file names groups {outside}, outside 0 to {groups - 1}; "
                         f"rerun the plan with --groups {groups}")
    existing = {test.name for test in tests}
    mapped = [name for name, g in groups_file.items() if g == group and name in existing]
    unmapped = [test.name for test in tests if test.name not in groups_file]
    return mapped + unmapped[group::groups]


def format_groups(assigned: list[list[Test]], times: BuildTimes) -> str:
    """The groups file for `assigned`, each group with its estimated holbuild time."""
    lines = ["# Test group of each generated test theory, written by",
             "# `tools/vyper_test_groups.py plan` from CI build times. Within a group,",
             "# longest first: holbuild starts the targets in this order.",
             f"# Estimates assume {times.workers} holbuild worker(s) per group."]
    for group, tests in enumerate(assigned):
        lines.append(f"# group {group}: about {times.makespan(tests) / 60:.0f} min of holbuild")
        lines += [f"{group} {test.name}" for test in tests]
    return "\n".join(lines) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    plan = commands.add_parser("plan", help=f"rewrite {GROUPS_FILE} from CI build times")
    plan.add_argument("--groups", type=int, default=6)
    plan.add_argument("--workers", type=int, choices=(1, 2), default=WORKERS,
                      help="HOL workers per group (default: 1, for CI runners below 12 GiB)")
    plan.add_argument("--runs", type=int, default=40, help="latest successful runs to read")
    targets = commands.add_parser("targets", help="print the theories one test group builds")
    targets.add_argument("--group", type=int, required=True)
    targets.add_argument("--groups", type=int, required=True)
    args = parser.parse_args()

    tests = generated_tests(GENERATED)
    if args.command == "targets":
        groups_file = read_groups(GROUPS_FILE)
        unmapped = [test.name for test in tests if test.name not in groups_file]
        if unmapped:
            print(f"::warning::{GROUPS_FILE} doesn't name {', '.join(unmapped)}; "
                  f"rerun tools/vyper_test_groups.py plan", file=sys.stderr)
        names = group_targets(tests, groups_file, args.group, args.groups)
        if not names:
            sys.exit(f"test group {args.group} has no tests")
        print(" ".join(f"{name}Theory" for name in names))
        return

    ci = CiLogs(REPO)
    runs = ci.recent_runs(args.runs)
    times = BuildTimes((log for run in runs for log in ci.test_logs(run)), tests, args.workers)
    missing = times.missing(tests)
    if missing:
        sys.exit(f"no build time in runs {', '.join(runs)} for: {', '.join(missing)}")
    GROUPS_FILE.write_text(format_groups(times.plan(tests, args.groups), times))


if __name__ == "__main__":
    main()
