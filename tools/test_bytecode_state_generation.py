"""Seeded generation and opt-in real pinned-compiler/py-evm state regressions."""
from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from bytecode_state_fuzz import (
    ROOT, generated_deployment, generated_source,
)


@unittest.skipUnless(os.environ.get("VYPER_STATE_VYPER"),
                     "set VYPER_STATE_VYPER to a clean VYPER_PIN checkout for real integration")
class GeneratedStateIntegrationTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.directory = Path(temporary.name)
        self.case_index = 0

    def worker(self, source, *, seed="explicit", generated=False, calls=None,
               constructor_args=(), deployment_value=0, calls_per_case=6):
        directory = self.directory / str(self.case_index)
        self.case_index += 1
        directory.mkdir()
        (directory / "source.vy").write_text(source)
        config = {
            "name": "generation_regression", "seed": seed,
            "vyper": os.environ["VYPER_STATE_VYPER"], "source_dir": str(ROOT),
            "optimize": "none", "experimental_codegen": True,
            "generated": generated, "constructor_args": list(constructor_args),
            "deployment_value": deployment_value, "calls": calls,
            "calls_per_case": calls_per_case,
            "python_hash_seed": "0",
        }
        config_path = directory / "case.json"
        config_path.write_text(json.dumps(config))
        result = subprocess.run(
            [sys.executable, str(ROOT / "tools/bytecode_state_fuzz.py"),
             "--_reference-worker", str(config_path)],
            capture_output=True, text=True, timeout=120,
            env={**os.environ, "PYTHONHASHSEED": "0"},
        )
        self.assertTrue((directory / "reference.json").is_file(), result.stdout + result.stderr)
        response = json.loads((directory / "reference.json").read_text())
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr + repr(response))
        return directory, response

    def generated_case(self, seed, **options):
        return self.worker(generated_source(seed), seed=seed, generated=True,
                           **generated_deployment(seed), **options)

    @staticmethod
    def execution(directory):
        traces = json.loads((directory / "traces.json").read_text())
        worlds = [trace for trace in traces if trace["trace_type"] == "state_checkpoint"]
        calls = [trace for trace in traces if trace["trace_type"] == "call"]
        deployment = next(trace for trace in traces if trace["trace_type"] == "deployment")
        return deployment, worlds, calls

    @staticmethod
    def accounts(world):
        return {account["address"]: account for account in world["accounts"]}

    def accepted_case(self):
        # Program may intentionally hit stock compiler rejections. Do not replace
        # it with a fixed source: require a real accepted seeded program instead.
        for index in range(10):
            directory, response = self.generated_case(f"0:{index}")
            if response["status"] == "passed":
                return directory
            self.assertEqual(response["status"], "compiler-rejected", response)
        self.fail("no compiler-accepted generated program among ten deterministic seeds")

    def test_default_seeds_execute_funding_transfer_and_endowed_self_copy(self):
        accepted = 0
        for index in range(8):
            with self.subTest(seed=f"0:{index}"):
                directory, response = self.generated_case(f"0:{index}")
                if response["status"] == "compiler-rejected":
                    continue
                self.assertEqual(response["status"], "passed", response)
                accepted += 1
                deployment, worlds, calls = self.execution(directory)
                plan = json.loads((directory / "calls.json").read_text())
                self.assertTrue(deployment["deployment_succeeded"])
                self.assertEqual(response["checkpoints"], 7)
                self.assertEqual([call["call_succeeded"] for call in calls[:3]], [True] * 3)
                contract = deployment["deployed_address"].lower()
                accounts = [self.accounts(world) for world in worlds]
                endowment = plan["deployment_value"]
                self.assertEqual(accounts[0][contract]["balance"], endowment)
                self.assertEqual(accounts[0][contract]["storage"],
                                 [{"slot": 0, "value": plan["constructor_args"][0]}])
                self.assertEqual(accounts[1][contract]["balance"], endowment + plan["calls"][0]["value"])
                recipient, amount = plan["calls"][1]["args"]
                recipient = recipient.lower()
                self.assertEqual(accounts[2][contract]["balance"], accounts[1][contract]["balance"] - amount)
                self.assertEqual(accounts[2][recipient]["balance"], accounts[1][recipient]["balance"] + amount)
                self.assertEqual(accounts[1][recipient]["code"], "")
                self.assertGreater(accounts[0][recipient]["balance"], 0)
                created = set(accounts[3]) - set(accounts[2])
                self.assertEqual(len(created), 1)
                child = accounts[3][created.pop()]
                self.assertEqual(child["balance"], plan["calls"][2]["args"][0])
                self.assertEqual(child["nonce"], 1)
                self.assertEqual(child["code"], accounts[0][contract]["code"])
                self.assertTrue(child["code"])
                self.assertEqual(child["storage"], [])  # Copy runtime, not constructor state.
                self.assertEqual(accounts[3][contract]["nonce"], accounts[2][contract]["nonce"] + 1)
                self.assertEqual(accounts[3][contract]["balance"], accounts[2][contract]["balance"])
        self.assertGreater(accepted, 0, "all seeded programs were compiler-rejected")

    def test_saved_plan_replay_and_bounds_preserve_real_state(self):
        directory = self.accepted_case()
        original_deployment, original_worlds, original_calls = self.execution(directory)
        source = (directory / "source.vy").read_text()
        scenario = json.loads((directory / "calls.json").read_text())
        # This is the explicit-source path: saved calls/constructor/endowment win,
        # and no generated prefix is injected when calls are already supplied.
        replay, response = self.worker(source, **scenario)
        self.assertEqual(response["status"], "passed", response)
        deployment, worlds, calls = self.execution(replay)
        self.assertEqual(worlds, original_worlds)
        self.assertEqual([call["call_succeeded"] for call in calls],
                         [call["call_succeeded"] for call in original_calls])
        self.assertEqual(deployment["deployment_succeeded"], original_deployment["deployment_succeeded"])
        contract = deployment["deployed_address"].lower()

        extra = [
            {"function": "state_create", "args": [2], "value": 2},
            {"function": "state_create", "args": [3], "value": 3},
            {"function": "state_fund", "args": [], "value": 33},
            {"function": "state_send", "args": [scenario["calls"][1]["args"][0], 17]},
            {"function": "state_create", "args": [17], "value": 17},
        ]
        bounded, response = self.worker(source, **{**scenario, "calls": scenario["calls"] + extra})
        self.assertEqual(response["status"], "passed", response)
        _, worlds, calls = self.execution(bounded)
        self.assertEqual([call["call_succeeded"] for call in calls[-5:]],
                         [True, False, False, False, False])
        before = self.accounts(worlds[-6])
        after = self.accounts(worlds[-5])
        self.assertEqual(len(set(after) - set(before)), 1)
        self.assertEqual(after[contract]["nonce"], before[contract]["nonce"] + 1)
        for world in worlds[-4:]:
            self.assertEqual(self.accounts(world), after)


if __name__ == "__main__":
    unittest.main()
