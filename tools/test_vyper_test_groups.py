"""Checks for the time-balanced assignment of Vyper test theories to CI groups."""

from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

from vyper_test_groups import BuildTimes, Test, format_groups, generated_tests, group_targets, read_groups


def log(seconds: dict[str, float]) -> str:
    """A CI log with one `built in` line per theory."""
    return "\n".join(f"2026-10-26T00:00:00.0Z {name}Theory built in {s}s" for name, s in seconds.items())


PART_SUFFIXES = [""] + [f"_part{k}" for k in range(1, 4)]
CHUNKS = [Test(f"vyperTest_slow{part}", "vyperTestDefs_slow") for part in PART_SUFFIXES]
SMALL = [Test(f"vyperTest_small{k}", f"vyperTestDefs_small{k}") for k in range(8)]
PARTS = [Test("vyperTest_slow", "vyperTestDefs_slow")] + [
    Test(f"vyperTest_slow_part{k}", f"vyperTestDefs_slow_part{k}")
    for k in range(1, 4)
]
TIMES = {"vyperTest_slow": 400.0, "vyperTestDefs_slow": 100.0}
TIMES |= {f"vyperTest_small{k}": 30.0 for k in range(8)} | {f"vyperTestDefs_small{k}": 10.0 for k in range(8)}


class TestBuildTimes(unittest.TestCase):
    """Build times read from CI logs, and the group builds they predict."""

    def setUp(self) -> None:
        self.times = BuildTimes([log(TIMES)], CHUNKS + SMALL)

    def test_new_chunks_share_the_unsplit_test_time(self) -> None:
        self.assertEqual([self.times.seconds[t.name] for t in CHUNKS], [100.0] * 4)

    def test_measured_chunk_times_are_kept(self) -> None:
        times = BuildTimes([log(TIMES | {"vyperTest_slow_part1": 7.0})], CHUNKS)
        self.assertEqual(times.seconds["vyperTest_slow_part1"], 7.0)
        self.assertEqual(times.seconds["vyperTest_slow"], 400.0)

    def test_new_chunks_have_separate_definition_theories(self) -> None:
        chunks = [Test(f"vyperTest_slow{part}", f"vyperTestDefs_slow{part}")
                  for part in PART_SUFFIXES]
        times = BuildTimes([log(TIMES)], chunks)
        self.assertEqual(times.missing(chunks), [])
        self.assertEqual([times.seconds[t.defs] for t in chunks], [25.0] * 4)
        self.assertEqual(sum(times.cost(t) for t in chunks), 500.0)

    def test_measured_definition_parts_are_kept(self) -> None:
        chunks = [Test(f"vyperTest_slow{part}", f"vyperTestDefs_slow{part}")
                  for part in PART_SUFFIXES]
        times = BuildTimes([log(TIMES | {"vyperTestDefs_slow_part1": 6.0})], chunks)
        self.assertEqual(times.seconds["vyperTestDefs_slow_part1"], 6.0)
        self.assertEqual(times.seconds["vyperTestDefs_slow"], 100.0)

    def test_tests_sharing_definitions_build_them_once(self) -> None:
        times = BuildTimes([log(TIMES)], CHUNKS, workers=4)
        self.assertEqual(times.makespan(CHUNKS), 200.0)

    def test_default_models_low_memory_ci_worker_cap(self) -> None:
        self.assertEqual(self.times.workers, 1)
        self.assertEqual(self.times.makespan(CHUNKS), 500.0)

    def test_two_worker_ci_schedule(self) -> None:
        times = BuildTimes([log(TIMES)], CHUNKS, workers=2)
        self.assertEqual(times.makespan(CHUNKS), 300.0)

    def test_empty_group_has_no_build_time(self) -> None:
        self.assertEqual(self.times.makespan([]), 0.0)

    def test_invalid_worker_and_group_counts_are_rejected(self) -> None:
        with self.assertRaisesRegex(ValueError, "workers must be positive"):
            BuildTimes([], [], workers=0)
        with self.assertRaisesRegex(ValueError, "groups must be positive"):
            self.times.plan(SMALL, 0)

    def test_chunks_go_to_different_groups(self) -> None:
        groups = self.times.plan(CHUNKS + SMALL, 4)
        self.assertEqual(sorted(sum(t in g for t in CHUNKS) for g in groups), [1, 1, 1, 1])

    def test_every_test_is_assigned_once(self) -> None:
        groups = self.times.plan(CHUNKS + SMALL, 3)
        self.assertCountEqual([t for g in groups for t in g], CHUNKS + SMALL)


class TestIndependentParts(unittest.TestCase):
    """Part zero retains the old name; every sibling has its own definitions."""

    def test_whole_file_time_is_shared_including_part_zero_and_definitions(self) -> None:
        times = BuildTimes([log(TIMES)], PARTS)
        self.assertEqual(times.missing(PARTS), [])
        self.assertEqual([times.seconds[t.name] for t in PARTS], [100.0] * 4)
        self.assertEqual([times.seconds[t.defs] for t in PARTS], [25.0] * 4)
        self.assertEqual(sum(map(times.cost, PARTS)), 500.0)
        self.assertEqual(times.makespan(PARTS), 500.0)

    def test_measured_parts_including_zero_are_not_rescaled(self) -> None:
        measured = {PARTS[0].name: 80.0, PARTS[0].defs: 20.0,
                    PARTS[1].name: 120.0, PARTS[1].defs: 30.0}
        times = BuildTimes([log(measured)], PARTS)
        for name, seconds in measured.items():
            self.assertEqual(times.seconds[name], seconds)
        self.assertEqual(times.cost(PARTS[2]), 125.0)

    def test_sibling_measurements_work_without_part_zero(self) -> None:
        times = BuildTimes([log({PARTS[1].name: 10.0, PARTS[1].defs: 5.0})], PARTS)
        self.assertEqual(times.missing(PARTS), [])
        self.assertEqual([times.cost(test) for test in PARTS], [15.0] * 4)

    def test_unmeasured_families_stay_missing(self) -> None:
        times = BuildTimes([], PARTS)
        self.assertEqual(len(times.missing(PARTS)), 8)

    def test_independent_parts_go_to_different_groups(self) -> None:
        times = BuildTimes([log(TIMES)], PARTS + SMALL)
        groups = times.plan(PARTS + SMALL, 4)
        self.assertEqual(sorted(sum(t in g for t in PARTS) for g in groups), [1] * 4)
        self.assertCountEqual([t for g in groups for t in g], PARTS + SMALL)

    def test_generated_headers_keep_each_part_independent(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            for test in PARTS:
                (root / f"{test.name}Script.sml").write_text(
                    f"Theory {test.name}[no_sig_docs]\nAncestors {test.defs}\nLibs vyperTestRunnerLib\n")
                (root / f"{test.defs}Script.sml").write_text(f"Theory {test.defs}\nAncestors jsonToVyper\n")
            self.assertEqual(generated_tests(root), PARTS)

    def test_plan_manifest_round_trip(self) -> None:
        times = BuildTimes([log(TIMES)], PARTS + SMALL, workers=2)
        assigned = times.plan(PARTS + SMALL, 6)
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "groups.txt"
            text = format_groups(assigned, times)
            self.assertIn("2 holbuild worker(s)", text)
            path.write_text(text)
            mapped = read_groups(path)
        for group, tests in enumerate(assigned):
            self.assertEqual(group_targets(PARTS + SMALL, mapped, group, 6),
                             [test.name for test in tests])


class TestGroupTargets(unittest.TestCase):
    """The theories one CI group builds, from the groups file and the generated tests."""

    def test_unmapped_tests_are_dealt_out(self) -> None:
        mapped = {SMALL[0].name: 0, SMALL[1].name: 1}
        self.assertEqual(group_targets(SMALL[:4], mapped, 0, 2), [SMALL[0].name, SMALL[2].name])
        self.assertEqual(group_targets(SMALL[:4], mapped, 1, 2), [SMALL[1].name, SMALL[3].name])

    def test_removed_tests_are_ignored(self) -> None:
        self.assertEqual(group_targets(SMALL[:1], {"vyperTest_gone": 0, SMALL[0].name: 0}, 0, 1),
                         [SMALL[0].name])

    def test_checked_in_manifest_covers_every_generated_part_once(self) -> None:
        root = Path(__file__).resolve().parents[1]
        tests = generated_tests(root / "tests/generated")
        path = root / ".github/vyper-test-groups.txt"
        mapped = read_groups(path)
        names = {test.name for test in tests}
        regression_root = root / "tests/vyper-regression"
        regression_names = {
            "vyperTest_functional_codegen_vyper_hol_regression_" +
            "_".join(source.relative_to(regression_root).with_suffix("").parts)
            for source in regression_root.rglob("test_*.py")
        }
        # Regression wrappers are generated in CI and intentionally uncommitted.
        # Only suites backed by a regression source may have a reserved mapping.
        absent_regressions = regression_names - names
        self.assertEqual(set(mapped) - absent_regressions, names)
        self.assertEqual(len(mapped), sum(bool(line and not line.startswith("#"))
                                          for line in path.read_text().splitlines()))
        assigned = [name for group in range(6)
                    for name in group_targets(tests, mapped, group, 6)]
        self.assertCountEqual(assigned, [test.name for test in tests])
        self.assertEqual(set(mapped.values()), set(range(6)))

    def test_groups_outside_the_matrix_are_rejected(self) -> None:
        with self.assertRaisesRegex(ValueError, r"names groups \[2\], outside 0 to 1"):
            group_targets(SMALL[:1], {SMALL[0].name: 2}, 0, 2)


if __name__ == "__main__":
    unittest.main()
