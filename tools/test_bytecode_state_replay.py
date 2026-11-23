"""Real worker/CLI regressions for failed deployments and saved-source replay.

Set VYPER_STATE_VYPER to the clean pinned compiler checkout. These tests use
py-evm and the emitted native runner, not subprocess or compiler stand-ins.
"""
from __future__ import annotations

import json
import hashlib
import os
from pathlib import Path
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest

from bytecode_state_fuzz import ROOT, RUNNER, replay, run_case


SEEDED_SOURCE = """stored: public(uint256)

@internal
@pure
def left(x: uint256) -> uint256:
    return x + 3

@internal
@pure
def right(x: uint256) -> uint256:
    return x * 2

@internal
@pure
def combine(x: uint256) -> uint256:
    return self.left(x) + self.right(x)

@deploy
@payable
def __init__(initial: uint256):
    self.stored = self.combine(initial)

@external
def update(x: uint256) -> uint256:
    self.stored = self.combine(x)
    return self.stored
"""

FAILED_SOURCE = """event Written:
    number: uint256

stored: uint256
scratch: transient(uint256)

@deploy
@payable
def __init__():
    self.stored = 77
    self.scratch = 88
    log Written(number=99)
    {failure}

@external
def put(number: uint256):
    self.stored = number
"""


@unittest.skipUnless(os.environ.get("VYPER_STATE_VYPER"),
                     "set VYPER_STATE_VYPER to a clean VYPER_PIN checkout for real integration")
class StateReplayIntegrationTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.directory = Path(temporary.name)
        self.binary = Path(os.environ.get("VYPER_STATE_RUNNER", str(RUNNER))).resolve()
        self.command = [sys.executable, str(ROOT / "tools/bytecode_state_fuzz.py"),
                        "--vyper", os.environ["VYPER_STATE_VYPER"],
                        "--runner", str(self.binary)]

    @staticmethod
    def load(directory, filename):
        return json.loads((directory / filename).read_text())

    @classmethod
    def evidence(cls, directory):
        # Fresh chains can have different genesis hashes. Source reproduction
        # checks compiler bytes and execution; exact environment replay uses JSON.
        traces = cls.load(directory, "traces.json")
        return {
            "deployments": [(row["initcode"], row["runtime_bytecode"],
                             row["deployment_succeeded"])
                            for row in traces if row["trace_type"] == "deployment"],
            "outputs": [(row["function_name"], row["output"], row["call_succeeded"])
                        for row in traces if row["trace_type"] == "call"],
            "worlds": [(row["accounts"], row["transient_storage"], row["logs"])
                       for row in traces if row["trace_type"] == "state_checkpoint"],
        }

    def cli(self, name, *options, hash_seed="random"):
        output = self.directory / name
        result = subprocess.run(
            self.command + list(options) + ["--out", str(output)],
            env={**os.environ, "PYTHONHASHSEED": hash_seed},
            capture_output=True, text=True, timeout=120,
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        summary = self.load(output, "report.json")
        self.assertEqual(summary["counts"], {"passed": 1}, summary)
        self.assertEqual(summary["compared"], 1)
        case = output / "state_000000"
        self.assertEqual(self.load(case, "reference.json")["status"], "passed")
        self.assertEqual(self.load(case, "report.json")["native"]["status"], "passed")
        return case

    def scenario(self, name, source, calls, **deployment):
        directory = self.directory / name
        directory.mkdir()
        path = directory / "input.vy"
        path.write_text(source)
        plan = directory / "plan.json"
        plan.write_text(json.dumps({"calls": calls, **deployment}))
        return path, plan

    def test_failed_constructors_with_nonempty_plans_reach_native_comparison(self):
        requested = [{"function": "put", "args": [123]}]
        for label, failure in (("revert", 'raise "rollback"'), ("invalid", "raise UNREACHABLE")):
            with self.subTest(failure=label):
                source, plan = self.scenario(label, FAILED_SOURCE.format(failure=failure),
                                             requested, deployment_value=9)
                case = self.cli(label + "-run", "--source", str(source), "--calls", str(plan))
                self.assertEqual(self.load(case, "case.json")["calls"], requested)
                self.assertEqual(self.load(case, "calls.json")["calls"], requested)
                traces = self.load(case, "traces.json")
                self.assertEqual([row for row in traces if row["trace_type"] == "call"], [])
                deployment = next(row for row in traces if row["trace_type"] == "deployment")
                self.assertIs(deployment["deployment_succeeded"], False)
                checkpoints = [row for row in traces if row["trace_type"] == "state_checkpoint"]
                self.assertEqual(len(checkpoints), 1)
                self.assertEqual(checkpoints[0]["boundary"], "deployment")
                self.assertEqual(checkpoints[0]["transient_storage"], [])
                self.assertEqual(checkpoints[0]["logs"], [])
                self.assertTrue(all(account["storage"] == [] for account in checkpoints[0]["accounts"]))
                # A real native replay must inspect constructor state even when
                # the deployment failed and the remaining plan was not executed.
                sender = next(account for account in checkpoints[0]["accounts"] if account["nonce"] == 1)
                sender["nonce"] += 1
                corrupted = self.directory / (label + "-corrupted.json")
                corrupted.write_text(json.dumps(traces))
                self.assertEqual(replay(self.binary, corrupted, 30)["status"], "mismatch")

    def test_failed_constructor_with_generated_calls_none_is_not_reference_error(self):
        case = self.directory / "generated-failure"
        case.mkdir()
        (case / "source.vy").write_text(FAILED_SOURCE.format(failure="raise UNREACHABLE"))
        config = {
            "name": "generated_failure", "seed": "0:0",
            "vyper": os.environ["VYPER_STATE_VYPER"], "source_dir": str(self.directory),
            "optimize": "none", "experimental_codegen": True,
            "generated": True, "calls": None, "calls_per_case": 6,
            "constructor_args": [], "deployment_value": 9,
        }
        # Exercise the same real fresh-worker/native path as the public driver.
        with self.binary.open("rb") as stream:
            digest = hashlib.file_digest(stream, "sha256").hexdigest()
        report = run_case(case, config, SimpleNamespace(
            reference_timeout=90, runner=self.binary, timeout=30), digest)
        self.assertEqual(report["status"], "passed", report)
        self.assertEqual(report["checkpoints"], 1)
        self.assertEqual(report["native"]["status"], "passed")
        self.assertIsNone(self.load(case, "case.json")["calls"])
        self.assertEqual(self.load(case, "calls.json")["calls"], [])
        self.assertEqual(self.load(case, "reference.json")["status"], "passed")

    def test_fresh_workers_reproduce_across_parent_hash_seeds_and_restore_settings(self):
        source, plan = self.scenario("seeded", SEEDED_SOURCE,
                                     [{"function": "update", "args": [7]},
                                      {"function": "stored"}],
                                     constructor_args=[5], deployment_value=11)
        first = self.cli("seed-one", "--source", str(source), "--calls", str(plan),
                         "--optimize", "gas", "--codegen", "legacy", hash_seed="1")
        second = self.cli("seed-two", "--source", str(source), "--calls", str(plan),
                          "--optimize", "gas", "--codegen", "legacy", hash_seed="98765")
        restored = self.cli("seed-replay", "--replay-case", str(first / "case.json"),
                            hash_seed="random")
        original = self.evidence(first)
        for case in (first, second, restored):
            with self.subTest(case=case.name):
                config = self.load(case, "case.json")
                provenance = self.load(case, "reference.json")["provenance"]
                self.assertEqual(str(config["python_hash_seed"]), "0")
                self.assertEqual(provenance["python_hash_seed"], "0")
                self.assertEqual(config["optimize"], "gas")
                self.assertIs(config["experimental_codegen"], False)
                self.assertEqual(config["constructor_args"], [5])
                self.assertEqual(config["deployment_value"], 11)
                self.assertEqual(self.evidence(case), original)
                self.assertEqual(self.load(case, "calls.json"), self.load(first, "calls.json"))

    def test_replay_defaults_old_metadata_to_zero_and_honors_recorded_hash_seed(self):
        source, plan = self.scenario("metadata", SEEDED_SOURCE,
                                     [{"function": "stored"}], constructor_args=[2], deployment_value=3)
        first = self.cli("metadata-initial", "--source", str(source), "--calls", str(plan))
        config = self.load(first, "case.json")
        del config["python_hash_seed"]
        (first / "case.json").write_text(json.dumps(config))
        old = self.cli("metadata-old", "--replay-case", str(first / "case.json"), hash_seed="19")
        self.assertEqual(self.load(old, "reference.json")["provenance"]["python_hash_seed"], "0")
        self.assertEqual(self.evidence(old), self.evidence(first))

        config["python_hash_seed"] = "73"
        (first / "case.json").write_text(json.dumps(config))
        seeded = self.cli("metadata-seeded", "--replay-case", str(first / "case.json"), hash_seed="23")
        repeated = self.cli("metadata-repeated", "--replay-case", str(seeded / "case.json"), hash_seed="31")
        for case in (seeded, repeated):
            self.assertEqual(self.load(case, "case.json")["python_hash_seed"], "73")
            self.assertEqual(self.load(case, "reference.json")["provenance"]["python_hash_seed"], "73")
        self.assertEqual(self.evidence(seeded), self.evidence(repeated))

    def test_saved_source_replay_uses_recorded_sibling_import_directory_not_decoy(self):
        source, plan = self.scenario("imports", """import helper

stored: public(uint256)

@deploy
@payable
def __init__(initial: uint256):
    self.stored = initial + helper.VALUE

@external
@pure
def read() -> uint256:
    return helper.VALUE
""", [{"function": "read"}, {"function": "stored"}],
            constructor_args=[5], deployment_value=7)
        (source.parent / "helper.vy").write_text("VALUE: constant(uint256) = 41\n")
        first = self.cli("imports-first", "--source", str(source), "--calls", str(plan))
        self.assertNotEqual(first, source.parent)
        # The archived source has a different parent, containing a valid but
        # observably wrong import. Using that parent must not accidentally pass.
        (first / "helper.vy").write_text("VALUE: constant(uint256) = 99\n")
        restored = self.cli("imports-replay", "--replay-case", str(first / "case.json"))
        self.assertEqual(self.load(restored, "case.json")["source_dir"], str(source.parent))
        self.assertEqual(self.evidence(restored), self.evidence(first))
        original_calls = [row for row in self.load(restored, "traces.json") if row["trace_type"] == "call"]
        self.assertEqual([int(row["output"], 16) for row in original_calls], [41, 46])
        # The old explicit-source interface remains usable and really selects
        # its own source directory, demonstrating why --replay-case is needed.
        decoy = self.cli("imports-decoy", "--source", str(first / "source.vy"),
                         "--calls", str(first / "calls.json"))
        decoy_calls = [row for row in self.load(decoy, "traces.json") if row["trace_type"] == "call"]
        self.assertEqual([int(row["output"], 16) for row in decoy_calls], [99, 104])


if __name__ == "__main__":
    unittest.main()
