"""Protocol guards and opt-in real compiler/py-evm/native integration checks."""
from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from bytecode_state_fuzz import ROOT, RUNNER, native_outcome, replay


class NativeProtocolTests(unittest.TestCase):
    def test_contradictory_process_results_are_not_semantic_mismatches(self):
        passed = json.dumps({"name": "case", "status": "passed"})
        failed = json.dumps({"name": "case", "status": "failed", "error": "different state"})
        for code, stdout, stderr in (
            (1, passed, ""), (0, failed, ""), (2, failed, ""),
            (1, failed, "decoder error"), (0, passed, "unexpected warning"),
        ):
            with self.subTest(code=code, stdout=stdout, stderr=stderr):
                self.assertEqual(native_outcome(code, stdout, stderr), "native-error")

    def test_incomplete_and_malformed_results_are_operational_errors(self):
        for output in (
            "", "not json", "[]", "null", '{"name":"other","status":"failed"}',
            '{"name":"case","status":"failed"}',
            '{"name":"case","status":"failed","error":123}',
            '{"name":"case","status":"passed","error":"contradiction"}',
            '{"name":"case","status":"passed"}\n{"name":"case","status":"passed"}',
        ):
            with self.subTest(output=output):
                self.assertEqual(native_outcome(1, output, ""), "native-error")


@unittest.skipUnless(os.environ.get("VYPER_STATE_VYPER"),
                     "set VYPER_STATE_VYPER to a clean VYPER_PIN checkout for real integration")
class StateDriverIntegrationTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.directory = Path(temporary.name)
        self.output = self.directory / "run"
        self.binary = Path(os.environ.get("VYPER_STATE_RUNNER", str(RUNNER))).resolve()
        self.command = [
            sys.executable, str(ROOT / "tools/bytecode_state_fuzz.py"),
            "--vyper", os.environ["VYPER_STATE_VYPER"], "--runner", str(self.binary),
        ]

    def test_full_state_and_reverts_replay_and_corrupted_storage_fails(self):
        command = self.command + ["--smoke", "--out", str(self.output)]
        result = subprocess.run(command, capture_output=True, text=True, timeout=120)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        report = json.loads((self.output / "report.json").read_text())
        self.assertEqual(report["compared"], 1)
        self.assertEqual(report["counts"], {"passed": 1})
        case = self.output / "state_000000"
        traces = json.loads((case / "traces.json").read_text())
        deployment = next(trace for trace in traces if trace["trace_type"] == "deployment")
        contract = deployment["deployed_address"].lower()
        checkpoints = [trace for trace in traces if trace["trace_type"] == "state_checkpoint"]
        self.assertEqual([trace["boundary"] for trace in checkpoints],
                         ["deployment", "call", "call", "call"])
        accounts = [next(account for account in trace["accounts"]
                         if account["address"] == contract) for trace in checkpoints]
        self.assertEqual([account["storage"] for account in accounts], [
            [{"slot": 0, "value": 3}], [{"slot": 0, "value": 9}],
            [{"slot": 0, "value": 9}], [],
        ])
        self.assertEqual(checkpoints[1]["transient_storage"],
                         [{"address": contract, "slot": 1, "value": 10}])
        self.assertEqual(checkpoints[2]["transient_storage"], [])
        self.assertEqual(checkpoints[3]["transient_storage"],
                         [{"address": contract, "slot": 1, "value": 1}])
        self.assertEqual(checkpoints[2]["logs"], checkpoints[1]["logs"])
        self.assertEqual([int(log["data"], 16) for log in checkpoints[3]["logs"]], [9, 0])
        calls = [trace for trace in traces if trace["trace_type"] == "call"]
        self.assertEqual([trace["call_succeeded"] for trace in calls], [True, False, True])

        accounts[-1]["storage"] = [{"slot": 0, "value": 42}]
        corrupted = self.directory / "corrupted.json"
        corrupted.write_text(json.dumps(traces))
        self.assertEqual(replay(self.binary, corrupted, 30)["status"], "mismatch")

        original = (self.output / "report.json").read_bytes()
        repeated = subprocess.run(command, capture_output=True, text=True, timeout=120)
        self.assertEqual(repeated.returncode, 2)
        self.assertEqual((self.output / "report.json").read_bytes(), original)

    def test_explicit_nested_bytes_and_reverting_constructor(self):
        source = self.directory / "case.vy"
        source.write_text("""struct Pair:
    tag: bytes2
    amount: uint256

saved: bytes2
total: uint256

@deploy
def __init__(tag: bytes2, fail: bool):
    self.saved = tag
    assert not fail

@external
def apply(items: DynArray[bytes2, 3], entry: Pair) -> bytes2:
    self.saved = items[0]
    self.total = entry.amount
    return entry.tag

@external
@view
def read() -> bytes2:
    return self.saved
""")
        for fail in (False, True):
            with self.subTest(constructor_reverts=fail):
                output = self.directory / f"explicit-{fail}"
                plan = self.directory / f"calls-{fail}.json"
                plan.write_text(json.dumps({
                    "constructor_args": ["0x0102", fail],
                    "calls": [] if fail else [
                        {"function": "apply", "args": [["0x0304"], ["0x0506", 17]]},
                        {"function": "read"},
                    ],
                }))
                command = self.command + [
                    "--source", str(source), "--calls", str(plan), "--out", str(output),
                ]
                result = subprocess.run(command, capture_output=True, text=True, timeout=120)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                traces = json.loads((output / "state_000000/traces.json").read_text())
                deployment = next(trace for trace in traces if trace["trace_type"] == "deployment")
                self.assertEqual(deployment["deployment_succeeded"], not fail)
                calls = [trace for trace in traces if trace["trace_type"] == "call"]
                if fail:
                    self.assertEqual(calls, [])
                    world = traces[-1]
                    self.assertEqual(world["boundary"], "deployment")
                    self.assertEqual(sorted(account["nonce"] for account in world["accounts"]),
                                     [0] * 9 + [1])
                    self.assertEqual([account["storage"] for account in world["accounts"]],
                                     [[]] * 10)
                else:
                    self.assertEqual([call["output"] for call in calls],
                                     ["0506" + "00" * 30, "0304" + "00" * 30])


if __name__ == "__main__":
    unittest.main()
