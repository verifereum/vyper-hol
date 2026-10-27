"""Checks for the maintainer-approved PR runs of the holbuild workflow.

The selector script and the workflow expressions run under Node, with
mocked GitHub responses; those tests are skipped without `node` on PATH.
The job wiring is read with PyYAML.
"""

from __future__ import annotations

import copy
import json
import re
import shutil
import subprocess
import unittest
from pathlib import Path
from typing import Any

import yaml


WORKFLOW = Path(__file__).resolve().parents[1] / ".github/workflows/holbuild.yml"
NODE = shutil.which("node")
MAIN_SHA = "a" * 40
FORK_SHA = "b" * 40
LATER_SHA = "c" * 40
APPROVED = {"select-source": {"result": "success", "outputs": {
    "repository": "contributor/vyper-hol", "sha": FORK_SHA, "approved": "true"}}}
OPEN_PR = {
    "state": "open",
    "base": {"repo": {"full_name": "verifereum/vyper-hol"}, "ref": "main"},
    "head": {"repo": {"full_name": "contributor/vyper-hol"}, "sha": FORK_SHA},
}
ORDINARY = {"select-source": {"result": "success", "outputs": {
    "repository": "verifereum/vyper-hol", "sha": MAIN_SHA, "approved": "false"}}}

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
// A GitHub expression as JavaScript: missing properties read as null, and
// hyphenated names are indexed.
const translate = expression => expression
  .replace(/\.([A-Za-z_][A-Za-z0-9_]*-[A-Za-z0-9_-]+)/g, "?.['$1']")
  .replace(/([A-Za-z0-9_\]])\.(?=[A-Za-z_])/g, '$1?.');
const format = (template, ...args) => template.replace(/\{(\d+)\}/g, (_, i) => args[i]);
const evaluate = expression => Function(
  'github', 'inputs', 'needs', 'steps', 'format', 'always', 'cancelled',
  `return (${translate(expression)});`,
)(input.github ?? {}, input.inputs ?? {}, input.needs ?? {}, input.steps ?? {}, format, () => true, () => false);
process.env.PR_NUMBER = input.number ?? '';
process.env.APPROVED_SHA = input.sha ?? '';
process.env.UNCACHED = input.uncached ?? '';
(async () => {
  try {
    if (input.template !== undefined) {
      const value = input.template.replace(/\$\{\{\s*([\s\S]*?)\s*\}\}/g, (_, expression) => {
        const result = evaluate(expression);
        return result === null || result === undefined ? '' : String(result);
      });
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


def load_workflow() -> dict[str, Any]:
    """The holbuild workflow, with every scalar kept as a string."""
    # BaseLoader keeps the `on` key as a string rather than True.
    return yaml.load(WORKFLOW.read_text(), Loader=yaml.BaseLoader)


def run_node(payload: dict[str, Any]) -> dict[str, Any]:
    """Run the Node harness on one payload and return its JSON result."""
    result = subprocess.run(
        [NODE, "-e", NODE_HARNESS], input=json.dumps(payload),
        text=True, capture_output=True, check=True,
    )
    return json.loads(result.stdout)


def render(template: str, **contexts: Any) -> str:
    """Evaluate every `${{ }}` in `template` against the given contexts."""
    result = run_node({"template": template, **contexts})
    if "error" in result:
        raise AssertionError(f"{template!r}: {result['error']}")
    return result["value"]


def step(job: dict[str, Any], **match: str) -> dict[str, Any]:
    """The one step of `job` whose fields start with the given values."""
    found = [s for s in job["steps"] if all(s.get(k, "").startswith(v) for k, v in match.items())]
    if len(found) != 1:
        raise AssertionError(f"expected one step matching {match}, found {len(found)}")
    return found[0]


@unittest.skipUnless(NODE, "needs node on PATH")
class TestSelectSource(unittest.TestCase):
    """The selector approves only a validated, current PR head from a main dispatch."""

    @classmethod
    def setUpClass(cls) -> None:
        cls.script = load_workflow()["jobs"]["select-source"]["steps"][0]["with"]["script"]

    def select(self, **changes: Any) -> dict[str, Any]:
        """Run the selector on an approved dispatch, with `changes` applied."""
        payload: dict[str, Any] = {
            "script": self.script,
            "context": {
                "repo": {"owner": "verifereum", "repo": "vyper-hol"},
                "eventName": "workflow_dispatch", "ref": "refs/heads/main", "sha": MAIN_SHA,
            },
            "number": "758", "sha": FORK_SHA, "uncached": "false", "pr": OPEN_PR,
        }
        for key, value in changes.items():
            if key == "context":
                payload[key].update(value)
            else:
                payload[key] = value
        return run_node(payload)

    def test_approved_head_selects_fork_repository_and_exact_sha(self) -> None:
        result = self.select()
        self.assertEqual(result["outputs"], {
            "repository": "contributor/vyper-hol", "sha": FORK_SHA, "approved": "true",
        })
        self.assertEqual(result["calls"], [{"owner": "verifereum", "repo": "vyper-hol", "pull_number": 758}])

    def test_approval_outside_main_is_rejected_before_api(self) -> None:
        for ref in ("refs/heads/feature", "refs/tags/main", "refs/pull/758/merge"):
            with self.subTest(ref=ref):
                result = self.select(context={"ref": ref})
                self.assertIn("Dispatch on main", result["error"])
                self.assertEqual((result["outputs"], result["calls"]), ({}, []))

    def test_approval_with_uncached_is_rejected_before_api(self) -> None:
        result = self.select(uncached="true")
        self.assertIn("uncached withholds", result["error"])
        self.assertEqual((result["outputs"], result["calls"]), ({}, []))

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
                result = self.select(number=number, sha=sha)
                self.assertIn("error", result)
                self.assertEqual((result["outputs"], result["calls"]), ({}, []))

    def test_moved_closed_deleted_or_wrong_base_pr_is_rejected(self) -> None:
        mutations = [
            ("state", "closed"), ("head.sha", LATER_SHA), ("head.repo", None),
            ("base.ref", "release"), ("base.repo.full_name", "other/vyper-hol"),
        ]
        for field, value in mutations:
            pr = copy.deepcopy(OPEN_PR)
            *path, last = field.split(".")
            target = pr
            for part in path:
                target = target[part]
            target[last] = value
            with self.subTest(field=field):
                result = self.select(pr=pr)
                self.assertIn("error", result)
                self.assertEqual(result["outputs"], {})

    def test_api_failure_cannot_approve(self) -> None:
        result = self.select(apiError="Resource not accessible by integration")
        self.assertEqual(result["error"], "Resource not accessible by integration")
        self.assertEqual(result["outputs"], {})

    def test_other_runs_select_the_triggering_commit_without_api(self) -> None:
        ordinary = {"repository": "verifereum/vyper-hol", "sha": MAIN_SHA, "approved": "false"}
        cases = [
            ({"eventName": "pull_request", "ref": "refs/pull/758/merge"}, "758", FORK_SHA, "false"),
            ({"eventName": "push"}, "", "", ""),
            ({"eventName": "merge_group", "ref": "refs/heads/gh-readonly-queue/main/pr-758"}, "", "", ""),
            ({"eventName": "schedule"}, "", "", ""),
            ({}, "", "", "true"),
            ({"ref": "refs/heads/feature"}, "", "", "false"),
        ]
        for context, number, sha, uncached in cases:
            with self.subTest(context=context, uncached=uncached):
                result = self.select(context=context, number=number, sha=sha, uncached=uncached)
                self.assertEqual((result["outputs"], result["calls"]), (ordinary, []))


@unittest.skipUnless(NODE, "needs node on PATH")
class TestRunExpressions(unittest.TestCase):
    """Workflow expressions give approved runs the login and their own identity, and leave other runs as before."""

    @classmethod
    def setUpClass(cls) -> None:
        cls.workflow = load_workflow()
        cls.jobs = cls.workflow["jobs"]

    def test_cache_login_goes_to_approved_and_trusted_runs(self) -> None:
        cases = [
            ("workflow_dispatch", "refs/heads/main", APPROVED, "bazel-cache"),
            ("workflow_dispatch", "refs/heads/main", ORDINARY, ""),
            ("schedule", "refs/heads/main", ORDINARY, ""),
            ("pull_request", "refs/pull/758/merge", ORDINARY, "bazel-cache"),
            ("push", "refs/heads/main", ORDINARY, "bazel-cache"),
            ("push", "refs/heads/feature", ORDINARY, ""),
            ("merge_group", "refs/heads/gh-readonly-queue/main/pr-758", ORDINARY, "bazel-cache"),
        ]
        jobs = [name for name, job in self.jobs.items() if "environment" in job]
        self.assertEqual(set(jobs), {
            "toolchain", "build", "compiler", "witnesses", "build-rollup", "test-deps", "vyper-tests",
        })
        for name in jobs:
            for event, ref, needs, expected in cases:
                with self.subTest(job=name, event=event, ref=ref):
                    github = {"event_name": event, "ref": ref,
                              "event": {"merge_group": {"base_ref": "refs/heads/main"}}}
                    self.assertEqual(render(self.jobs[name]["environment"], github=github, needs=needs), expected)

    def test_approved_runs_get_their_own_concurrency_group(self) -> None:
        group = self.workflow["concurrency"]["group"]
        dispatch = {"workflow": "holbuild", "event_name": "workflow_dispatch",
                    "ref": "refs/heads/main", "run_id": 42, "event": {}}
        self.assertEqual(render(group, github=dispatch, inputs={"approved_sha": FORK_SHA}), "holbuild-42")
        self.assertEqual(render(group, github=dispatch, inputs={"approved_sha": ""}), "holbuild-refs/heads/main")
        pr = dispatch | {"event_name": "pull_request", "event": {"action": "synchronize", "pull_request": {"number": 758}}}
        self.assertEqual(render(group, github=pr), "holbuild-758")

    def test_run_title_names_the_approved_sha(self) -> None:
        title = self.workflow["run-name"]
        dispatch = {"event_name": "workflow_dispatch"}
        approved = render(title, github=dispatch, inputs={"pr_number": "758", "approved_sha": FORK_SHA})
        self.assertEqual(approved, f"Approved PR 758 at {FORK_SHA}")
        self.assertEqual(render(title, github=dispatch, inputs={"pr_number": "", "approved_sha": ""}), "")
        self.assertEqual(render(title, github={"event_name": "push"}), "")

    def test_approved_build_snapshot_is_outside_the_restore_prefix(self) -> None:
        command = step(self.jobs["build"], id="cache-key")["run"]
        steps = {"project": {"outputs": {"build-prefix": "holbuild-v3-build-T", "stage-prefix": "holbuild-v3-stage-T"}}}
        github = {"run_id": 42, "run_attempt": 1}
        approved = render(command, github=github, needs=APPROVED, steps=steps)
        self.assertIn(f"snapshot-key=holbuild-v3-stage-T-build-{FORK_SHA}-42-1", approved)
        ordinary = render(command, github=github, needs=ORDINARY, steps=steps)
        self.assertIn(f"snapshot-key=holbuild-v3-build-T-{MAIN_SHA}-42-1", ordinary)


class TestJobWiring(unittest.TestCase):
    """Every job builds the selected commit, and only through the selector's validation."""

    @classmethod
    def setUpClass(cls) -> None:
        cls.workflow = load_workflow()
        cls.jobs = cls.workflow["jobs"]

    def test_every_checkout_uses_the_selected_source_without_credentials(self) -> None:
        checkouts = set()
        for name, job in self.jobs.items():
            for s in job.get("steps", []):
                if s.get("uses", "").startswith("actions/checkout@"):
                    checkouts.add(name)
                    self.assertIn("select-source", job["needs"])
                    self.assertEqual(s["with"], {
                        "repository": "${{ needs.select-source.outputs.repository }}",
                        "ref": "${{ needs.select-source.outputs.sha }}",
                        "persist-credentials": "false",
                    })
        self.assertEqual(checkouts, {
            "toolchain", "build", "compiler", "witnesses", "build-rollup", "test-deps",
            "python-o1-oracle", "export-vyper-tests", "vyper-tests",
        })

    def test_selector_has_no_secrets_and_the_pr_trust_gate(self) -> None:
        selector = self.jobs["select-source"]
        self.assertNotIn("environment", selector)
        self.assertNotIn("needs", selector)
        self.assertEqual(selector["if"], self.jobs["toolchain"]["if"])
        self.assertEqual(selector["permissions"], {"contents": "read", "pull-requests": "read"})
        self.assertEqual(self.workflow["permissions"], {"contents": "read"})
        self.assertEqual(set(self.workflow["on"]), {
            "workflow_dispatch", "schedule", "pull_request", "merge_group", "push",
        })

    def test_jobs_that_override_status_checks_require_the_selector(self) -> None:
        for name in ("python-o1-oracle", "export-vyper-tests"):
            with self.subTest(job=name):
                self.assertIn("needs.select-source.result == 'success'", self.jobs[name]["if"])

    def test_snapshot_keys_and_artefact_name_the_selected_sha(self) -> None:
        for name in ("toolchain", "build", "compiler", "test-deps"):
            with self.subTest(job=name):
                command = step(self.jobs[name], id="cache-key")["run"]
                self.assertIn("-${{ needs.select-source.outputs.sha }}-${{ github.run_id }}", command)
                self.assertNotIn("github.sha", command)
        upload = step(self.jobs["build-rollup"], name="Upload HBX artefact")
        self.assertEqual(upload["with"]["name"], "${{ env.HBX_BASENAME }}-hbx-${{ needs.select-source.outputs.sha }}")
        rollup = step(self.jobs["build-rollup"], name="Save holbuild project snapshot")
        self.assertEqual(rollup["with"]["key"], "${{ needs.build.outputs.holbuild-cache-key }}-rollup")

    def test_only_the_ordinary_build_snapshot_uses_the_restore_prefix(self) -> None:
        text = WORKFLOW.read_text()
        self.assertEqual(text.count("outputs.build-prefix"), 1)
        self.assertIn("outputs.build-prefix", step(self.jobs["build"], id="cache-key")["run"])
        toolchain_save = step(self.jobs["build"], name="Save holbuild toolchain cache")
        self.assertEqual(toolchain_save["if"], "${{ github.event_name == 'push' }}")


class TestSuccessRollup(unittest.TestCase):
    """holbuild-success fails unless the selector and every build job succeeded."""

    @classmethod
    def setUpClass(cls) -> None:
        job = load_workflow()["jobs"]["holbuild-success"]
        cls.needs = job["needs"]
        cls.check = job["steps"][0]

    def passes(self, results: dict[str, str], *, merge_group_passed: str = "") -> bool:
        """Whether the rollup step exits 0 for the given job results."""
        env = {
            key: re.sub(r"\$\{\{ needs\.([\w-]+)\.result \}\}", lambda m: results[m[1]], value)
            for key, value in self.check["env"].items() if key != "MERGE_GROUP_PASSED"
        }
        env["MERGE_GROUP_PASSED"] = merge_group_passed
        return subprocess.run(["bash", "-c", self.check["run"]], env=env).returncode == 0

    def test_every_job_is_needed(self) -> None:
        self.assertEqual(self.needs[0], "select-source")
        jobs = set(load_workflow()["jobs"]) - {"holbuild-success"}
        self.assertEqual(set(self.needs), jobs)

    def test_selector_failure_fails_the_run(self) -> None:
        results = {name: "success" for name in self.needs}
        self.assertTrue(self.passes(results))
        for status in ("failure", "skipped", "cancelled"):
            with self.subTest(status=status):
                self.assertFalse(self.passes(results | {"select-source": status}, merge_group_passed="true"))


if __name__ == "__main__":
    unittest.main()
