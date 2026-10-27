"""Check the trusted workflow selector with mocked GitHub responses.

Run with Node on PATH and PyYAML installed:
    python3 -m unittest discover -s tools -p test_approved_fork_ci.py
"""

import copy
import json
import subprocess
import unittest
from pathlib import Path
from typing import Any

import yaml


WORKFLOW = Path(__file__).resolve().parents[1] / ".github/workflows/holbuild.yml"
MAIN_SHA = "a" * 40
FORK_SHA = "b" * 40
LATER_SHA = "c" * 40

NODE_HARNESS = r"""
const fs = require('node:fs');
const input = JSON.parse(fs.readFileSync(0, 'utf8'));
const AsyncFunction = Object.getPrototypeOf(async function(){}).constructor;
let outputs = {}, calls = [];
const summary = {
  addHeading() { return this; }, addTable() { return this; },
  addRaw() { return this; }, async write() {},
};
const core = {setOutput: (key, value) => { outputs[key] = value; }, summary};
const github = {rest: {pulls: {get: async request => {
  calls.push(request);
  if (input.apiError) throw new Error(input.apiError);
  return {data: input.pr};
}}}};
process.env.PR_NUMBER = input.number ?? '';
process.env.APPROVED_SHA = input.sha ?? '';
(async () => {
  try {
    if (input.expression) {
      const expression = input.expression.replace(/^\$\{\{\s*|\s*\}\}$/g, '')
        .replace(/needs\.([a-zA-Z0-9_-]+)/g, "needs['$1']");
      const value = Function('github', 'needs', 'always', `return (${expression});`)
        (input.event, input.needs, () => true);
      console.log(JSON.stringify({value}));
    } else {
      await new AsyncFunction('context', 'github', 'core', input.script)
        (input.context, github, core);
      console.log(JSON.stringify({outputs, calls}));
    }
  } catch (error) {
    console.log(JSON.stringify({error: error.message, outputs, calls}));
  }
})();
"""


class ApprovedForkCI(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        # BaseLoader preserves the GitHub Actions `on` key and scalar strings.
        cls.workflow = yaml.load(WORKFLOW.read_text(), Loader=yaml.BaseLoader)
        cls.jobs = cls.workflow["jobs"]
        cls.script = cls.jobs["select-source"]["steps"][0]["with"]["script"]

    def invoke(self, payload: dict[str, Any]) -> dict[str, Any]:
        result = subprocess.run(
            ["node", "-e", NODE_HARNESS], input=json.dumps(payload),
            text=True, capture_output=True, check=True,
        )
        return json.loads(result.stdout)

    def selection(self, **changes: Any) -> dict[str, Any]:
        payload = {
            "script": self.script,
            "context": {
                "repo": {"owner": "verifereum", "repo": "vyper-hol"},
                "eventName": "workflow_dispatch", "ref": "refs/heads/main",
                "sha": MAIN_SHA,
            },
            "number": "758", "sha": FORK_SHA,
            "pr": {
                "state": "open",
                "base": {"repo": {"full_name": "verifereum/vyper-hol"}, "ref": "main"},
                "head": {"repo": {"full_name": "contributor/vyper-hol"}, "sha": FORK_SHA},
            },
        }
        for key, value in changes.items():
            if key == "context":
                payload[key].update(value)
            else:
                payload[key] = value
        return self.invoke(payload)

    def test_approved_head_uses_fork_repository_and_exact_sha(self) -> None:
        result = self.selection()
        self.assertEqual(result["outputs"], {
            "repository": "contributor/vyper-hol", "sha": FORK_SHA, "approved": "true",
        })
        self.assertEqual(result["calls"], [{
            "owner": "verifereum", "repo": "vyper-hol", "pull_number": 758,
        }])

    def test_rejects_untrusted_dispatch_workflow(self) -> None:
        for ref in ("refs/heads/feature", "refs/tags/main", "refs/pull/758/merge"):
            with self.subTest(ref=ref):
                result = self.selection(context={"ref": ref})
                self.assertIn("workflow is trusted", result["error"])
                self.assertEqual(result["outputs"], {})
                self.assertEqual(result["calls"], [])

    def test_invalid_or_partial_approval_fails_before_api(self) -> None:
        cases = [
            ("", FORK_SHA), ("758", ""), ("0", FORK_SHA), ("-1", FORK_SHA),
            ("1.5", FORK_SHA), ("758;echo bad", FORK_SHA), ("9007199254740992", FORK_SHA),
            ("758", "main"), ("758", "b" * 39), ("758", "B" * 40),
            ("758\n", FORK_SHA), (" 758", FORK_SHA),
            ("758", "b" * 40 + "\n"), ("758", "${{ secrets.TOKEN }}"),
        ]
        for number, sha in cases:
            with self.subTest(number=number, sha=sha):
                result = self.selection(number=number, sha=sha)
                self.assertIn("error", result)
                self.assertEqual(result["outputs"], {})
                self.assertEqual(result["calls"], [])

    def test_rejects_moved_closed_deleted_or_wrong_base_pr(self) -> None:
        pr = {
            "state": "open",
            "base": {"repo": {"full_name": "verifereum/vyper-hol"}, "ref": "main"},
            "head": {"repo": {"full_name": "contributor/vyper-hol"}, "sha": FORK_SHA},
        }
        mutations = [
            ("state", "closed"), ("head.sha", LATER_SHA), ("head.repo", None),
            ("base.ref", "release"), ("base.repo.full_name", "other/vyper-hol"),
        ]
        for field, value in mutations:
            candidate = copy.deepcopy(pr)
            target = candidate
            parts = field.split(".")
            for part in parts[:-1]:
                target = target[part]
            target[parts[-1]] = value
            with self.subTest(field=field):
                result = self.selection(pr=candidate)
                self.assertIn("error", result)
                self.assertEqual(result["outputs"], {})

    def test_api_failure_cannot_approve(self) -> None:
        result = self.selection(apiError="Resource not accessible by integration")
        self.assertEqual(result["error"], "Resource not accessible by integration")
        self.assertEqual(result["outputs"], {})

    def test_ordinary_events_keep_trigger_sha_without_approval(self) -> None:
        for event in ("pull_request", "push", "merge_group"):
            with self.subTest(event=event):
                result = self.selection(context={"eventName": event})
                self.assertEqual(result["outputs"], {
                    "repository": "verifereum/vyper-hol", "sha": MAIN_SHA, "approved": "false",
                })
                self.assertEqual(result["calls"], [])
        result = self.selection(number="", sha="")
        self.assertEqual(result["outputs"]["sha"], MAIN_SHA)
        self.assertEqual(result["outputs"]["approved"], "false")

    def test_every_checkout_uses_validated_source_without_credentials(self) -> None:
        expected = {"build", "python-o1-oracle", "export-vyper-tests", "vyper-tests"}
        actual = set()
        for name, job in self.jobs.items():
            for step in job.get("steps", []):
                if step.get("uses", "").startswith("actions/checkout@"):
                    actual.add(name)
                    self.assertIn("select-source", job["needs"])
                    self.assertEqual(step["with"], {
                        "repository": "${{ needs.select-source.outputs.repository }}",
                        "ref": "${{ needs.select-source.outputs.sha }}",
                        "persist-credentials": "false",
                    })
        self.assertEqual(actual, expected)
        self.assertNotIn("environment", self.jobs["select-source"])
        self.assertEqual(self.workflow["permissions"], {"contents": "read"})
        self.assertEqual(self.jobs["select-source"]["permissions"], {
            "contents": "read", "pull-requests": "read",
        })
        self.assertEqual(set(self.workflow["on"]), {
            "workflow_dispatch", "pull_request", "merge_group", "push",
        })

    def test_cache_environment_is_only_available_to_approved_or_trusted_events(self) -> None:
        cases = [
            ("workflow_dispatch", "refs/heads/main", "true", "", "bazel-cache"),
            ("workflow_dispatch", "refs/heads/main", "false", "", ""),
            ("pull_request", "refs/pull/758/merge", "false", "", ""),
            ("push", "refs/heads/main", "false", "", "bazel-cache"),
            ("push", "refs/heads/feature", "false", "", ""),
            ("merge_group", "refs/heads/gh-readonly-queue/main/pr-758", "false", "refs/heads/main", "bazel-cache"),
            ("merge_group", "refs/heads/gh-readonly-queue/release/pr-758", "false", "refs/heads/release", ""),
        ]
        for job in ("build", "vyper-tests"):
            for event, ref, approved, base, expected in cases:
                with self.subTest(job=job, event=event, ref=ref):
                    result = self.invoke({
                        "expression": self.jobs[job]["environment"],
                        "event": {"event_name": event, "ref": ref, "event": {"merge_group": {"base_ref": base}}},
                        "needs": {"select-source": {"outputs": {"approved": approved}}},
                    })
                    self.assertEqual(result, {"value": expected})

    def test_rollup_fails_for_any_missing_failed_or_skipped_job(self) -> None:
        rollup = self.jobs["holbuild-success"]
        required = {"select-source", "build", "python-o1-oracle", "export-vyper-tests", "vyper-tests"}
        self.assertEqual(set(rollup["needs"]), required)
        self.assertEqual(rollup["if"], "always()")
        needs = {name: {"result": "success"} for name in required}
        expression = rollup["steps"][0]["if"]
        self.assertEqual(self.invoke({"expression": expression, "needs": needs}), {"value": False})
        for name in required:
            for status in ("failure", "skipped", "cancelled", ""):
                candidate = copy.deepcopy(needs)
                candidate[name]["result"] = status
                with self.subTest(job=name, status=status):
                    self.assertEqual(self.invoke({"expression": expression, "needs": candidate}), {"value": True})

    def test_artifacts_and_project_cache_identify_selected_sha(self) -> None:
        build_steps = self.jobs["build"]["steps"]
        cache = next(step for step in build_steps if step.get("id") == "cache-key")
        snapshot = next(line for line in cache["run"].splitlines() if line.startswith("snapshot_key="))
        self.assertIn("${{ needs.select-source.outputs.sha }}", snapshot)
        self.assertNotIn("github.sha", snapshot)
        upload = next(step for step in build_steps if step.get("uses", "").startswith("actions/upload-artifact@"))
        self.assertEqual(upload["with"]["name"], "vyper-hol-hbx-${{ needs.select-source.outputs.sha }}")
        self.assertEqual(self.jobs["vyper-tests"]["strategy"]["matrix"]["group"], [str(n) for n in range(10)])
        self.assertIn("github.run_id", self.workflow["concurrency"]["group"])
        self.assertNotIn("github.ref", self.workflow["concurrency"]["group"])


if __name__ == "__main__":
    unittest.main()
