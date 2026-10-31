"""Checks for the time-balanced assignment of Vyper test theories to CI groups."""

from __future__ import annotations

import unittest

from vyper_test_groups import BuildTimes, Test, group_targets


def log(seconds: dict[str, float]) -> str:
    """A CI log with one `built in` line per theory."""
    return "\n".join(f"2026-10-26T00:00:00.0Z {name}Theory built in {s}s" for name, s in seconds.items())


PARTS = [""] + [f"_part{k}" for k in range(1, 4)]
CHUNKS = [Test(f"vyperTest_slow{part}", "vyperTestDefs_slow") for part in PARTS]
SMALL = [Test(f"vyperTest_small{k}", f"vyperTestDefs_small{k}") for k in range(8)]
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
                  for part in PARTS]
        times = BuildTimes([log(TIMES)], chunks)
        self.assertEqual(times.missing(chunks), [])
        self.assertEqual([times.seconds[t.defs] for t in chunks], [25.0] * 4)
        self.assertEqual(sum(times.cost(t) for t in chunks), 500.0)

    def test_measured_definition_parts_are_kept(self) -> None:
        chunks = [Test(f"vyperTest_slow{part}", f"vyperTestDefs_slow{part}")
                  for part in PARTS]
        times = BuildTimes([log(TIMES | {"vyperTestDefs_slow_part1": 6.0})], chunks)
        self.assertEqual(times.seconds["vyperTestDefs_slow_part1"], 6.0)
        self.assertEqual(times.seconds["vyperTestDefs_slow"], 100.0)

    def test_tests_sharing_definitions_build_them_once(self) -> None:
        self.assertEqual(self.times.makespan(CHUNKS), 200.0)

    def test_chunks_go_to_different_groups(self) -> None:
        groups = self.times.plan(CHUNKS + SMALL, 4)
        self.assertEqual(sorted(sum(t in g for t in CHUNKS) for g in groups), [1, 1, 1, 1])

    def test_every_test_is_assigned_once(self) -> None:
        groups = self.times.plan(CHUNKS + SMALL, 3)
        self.assertCountEqual([t for g in groups for t in g], CHUNKS + SMALL)


class TestGroupTargets(unittest.TestCase):
    """The theories one CI group builds, from the groups file and the generated tests."""

    def test_unmapped_tests_are_dealt_out(self) -> None:
        mapped = {SMALL[0].name: 0, SMALL[1].name: 1}
        self.assertEqual(group_targets(SMALL[:4], mapped, 0, 2), [SMALL[0].name, SMALL[2].name])
        self.assertEqual(group_targets(SMALL[:4], mapped, 1, 2), [SMALL[1].name, SMALL[3].name])

    def test_removed_tests_are_ignored(self) -> None:
        self.assertEqual(group_targets(SMALL[:1], {"vyperTest_gone": 0, SMALL[0].name: 0}, 0, 1),
                         [SMALL[0].name])

    def test_groups_outside_the_matrix_are_rejected(self) -> None:
        with self.assertRaisesRegex(ValueError, r"names groups \[2\], outside 0 to 1"):
            group_targets(SMALL[:1], {SMALL[0].name: 2}, 0, 2)


if __name__ == "__main__":
    unittest.main()
