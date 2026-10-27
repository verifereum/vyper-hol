"""Checks for the maintainer-approved PR runs of the holbuild workflow.

The selector script and the workflow expressions run under Node, with
mocked GitHub responses; those tests are skipped without `node` on PATH.
The release run filter runs under jq, and is skipped without `jq`. The job
wiring is read with PyYAML.
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


WORKFLOWS = Path(__file__).resolve().parents[1] / ".github/workflows"
WORKFLOW = WORKFLOWS / "holbuild.yml"
NODE = shutil.which("node")
JQ = shutil.which("jq")
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
ORDINARY = {"select-source": {"result": "skipped", "outputs": {}}}
CACHE_JOBS = {"toolchain", "build", "compiler", "witnesses", "build-rollup", "test-deps", "vyper-tests"}
STATUS_FUNCTIONS = ("always()", "cancelled()", "success()", "failure()")

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


def load_workflow(name: str = "holbuild.yml") -> dict[str, Any]:
    """A workflow, with every scalar kept as a string."""
    # BaseLoader keeps the `on` key as a string rather than True.
    return yaml.load((WORKFLOWS / name).read_text(), Loader=yaml.BaseLoader)


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


def holds(condition: str, **contexts: Any) -> bool:
    """Whether a job or step `if` holds: its value is truthy."""
    expression = re.fullmatch(r"\$\{\{(.*)\}\}", condition.strip(), re.S)
    return render("${{ !!(" + (expression[1] if expression else condition) + ") }}", **contexts) == "true"


def step(job: dict[str, Any], **match: str) -> dict[str, Any]:
    """The one step of `job` whose fields start with the given values."""
    found = [s for s in job["steps"] if all(s.get(k, "").startswith(v) for k, v in match.items())]
    if len(found) != 1:
        raise AssertionError(f"expected one step matching {match}, found {len(found)}")
    return found[0]


class Run:
    """One simulated run: which jobs start, from their `if` and their needs.

    select-source, when it starts, ends with `source`; holbuild-success runs
    its check step; every other job that starts succeeds.
    """

    def __init__(self, github: dict[str, Any], inputs: dict[str, Any], source: dict[str, Any]) -> None:
        self.jobs = load_workflow()["jobs"]
        self.github = github
        self.inputs = inputs
        self.results: dict[str, str] = {}
        self.outputs: dict[str, dict[str, str]] = {}
        # Jobs are listed after the jobs they need.
        for name, job in self.jobs.items():
            if not self._starts(name):
                self.results[name], self.outputs[name] = "skipped", {}
            elif name == "select-source":
                self.results[name], self.outputs[name] = source["result"], source["outputs"]
            elif name == "holbuild-success":
                self.results[name], self.outputs[name] = self._rollup(), {}
            else:
                self.results[name], self.outputs[name] = "success", {}
        self.outputs["tested"] = {"merge-group-passed": "false"} if self.results["tested"] == "success" else {}

    def needs(self, name: str) -> dict[str, Any]:
        """The needs context of job `name`."""
        needs = self.jobs[name].get("needs", [])
        names = [needs] if isinstance(needs, str) else needs
        return {n: {"result": self.results[n], "outputs": self.outputs[n]} for n in names}

    def render(self, name: str, template: str) -> str:
        """Evaluate `template` as job `name` would."""
        return render(template, github=self.github, inputs=self.inputs, needs=self.needs(name))

    @property
    def started(self) -> set[str]:
        """The jobs that started."""
        return {name for name, result in self.results.items() if result != "skipped"}

    def _starts(self, name: str) -> bool:
        """Whether job `name` starts."""
        condition = self.jobs[name].get("if", "success()")
        starts = holds(condition, github=self.github, inputs=self.inputs, needs=self.needs(name))
        if any(function in condition for function in STATUS_FUNCTIONS):
            return starts
        return starts and all(need["result"] == "success" for need in self.needs(name).values())

    def _rollup(self) -> str:
        """The result of holbuild-success's check step."""
        check = self.jobs["holbuild-success"]["steps"][0]
        env = {key: self.render("holbuild-success", value) for key, value in check["env"].items()}
        return "success" if subprocess.run(["bash", "-c", check["run"]], env=env).returncode == 0 else "failure"


@unittest.skipUnless(NODE, "needs node on PATH")
class TestSelectSource(unittest.TestCase):
    """The selector approves only a validated, current PR head from a main dispatch."""

    @classmethod
    def setUpClass(cls) -> None:
        cls.job = load_workflow()["jobs"]["select-source"]
        cls.script = cls.job["steps"][0]["with"]["script"]

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

    def test_runs_only_on_a_dispatch_with_pr_inputs(self) -> None:
        cases = [
            ("workflow_dispatch", {"pr_number": "758", "approved_sha": FORK_SHA}, True),
            ("workflow_dispatch", {"pr_number": "758", "approved_sha": ""}, True),
            ("workflow_dispatch", {"pr_number": "", "approved_sha": FORK_SHA}, True),
            ("workflow_dispatch", {"pr_number": "", "approved_sha": "", "uncached": True}, False),
            ("pull_request", {}, False), ("push", {}, False),
            ("merge_group", {}, False), ("schedule", {}, False),
        ]
        for event, inputs, expected in cases:
            with self.subTest(event=event, inputs=inputs):
                self.assertEqual(holds(self.job["if"], github={"event_name": event}, inputs=inputs), expected)

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


@unittest.skipUnless(NODE, "needs node on PATH")
class TestJobGraph(unittest.TestCase):
    """Approved runs start every job at the PR head; other runs skip only the selector."""

    DISPATCH = {"event_name": "workflow_dispatch", "ref": "refs/heads/main", "sha": MAIN_SHA,
                "repository": "verifereum/vyper-hol", "run_id": 42, "run_attempt": 1, "event": {}}
    APPROVAL = {"uncached": False, "pr_number": "758", "approved_sha": FORK_SHA}
    BUILD_AND_TEST = CACHE_JOBS | {"python-o1-oracle", "export-vyper-tests", "holbuild-success"}

    def test_ordinary_runs_skip_the_selector_and_start_the_rest(self) -> None:
        events = [
            ("workflow_dispatch", "refs/heads/main", {}, {"uncached": False, "pr_number": "", "approved_sha": ""}),
            ("pull_request", "refs/pull/9/merge", {"action": "synchronize", "pull_request": {
                "draft": False, "head": {"repo": {"full_name": "verifereum/vyper-hol"}}}}, {}),
            ("merge_group", "refs/heads/gh-readonly-queue/main/pr-9", {"merge_group": {"base_ref": "refs/heads/main"}}, {}),
            ("push", "refs/heads/main", {}, {}),
        ]
        for event, ref, payload, inputs in events:
            with self.subTest(event=event):
                run = Run(self.DISPATCH | {"event_name": event, "ref": ref, "event": payload}, inputs, ORDINARY["select-source"])
                expected = self.BUILD_AND_TEST | ({"tested"} if event == "push" else set())
                self.assertEqual(run.started, expected)
                self.assertEqual(run.results["holbuild-success"], "success")
                checkout = step(run.jobs["build"], uses="actions/checkout@")["with"]
                self.assertEqual(run.render("build", checkout["repository"]), "")
                self.assertEqual(run.render("build", checkout["ref"]), "")

    def test_fork_pr_starts_nothing(self) -> None:
        payload = {"action": "synchronize", "pull_request": {"draft": False, "head": {"repo": {"full_name": "contributor/vyper-hol"}}}}
        run = Run(self.DISPATCH | {"event_name": "pull_request", "ref": "refs/pull/9/merge", "event": payload}, {}, ORDINARY["select-source"])
        self.assertEqual(run.started, set())

    def test_approved_run_starts_every_job_with_the_login_at_the_pr_head(self) -> None:
        run = Run(self.DISPATCH, self.APPROVAL, APPROVED["select-source"])
        self.assertEqual(run.started, self.BUILD_AND_TEST | {"select-source"})
        self.assertEqual(run.results["holbuild-success"], "success")
        for name in sorted(CACHE_JOBS):
            with self.subTest(job=name):
                self.assertEqual(run.render(name, run.jobs[name]["environment"]), "bazel-cache")
                checkout = step(run.jobs[name], uses="actions/checkout@")["with"]
                self.assertEqual(run.render(name, checkout["repository"]), "contributor/vyper-hol")
                self.assertEqual(run.render(name, checkout["ref"]), FORK_SHA)

    def test_failed_selection_stops_every_job_and_fails_the_run(self) -> None:
        for result in ("failure", "cancelled"):
            with self.subTest(result=result):
                run = Run(self.DISPATCH, self.APPROVAL, {"result": result, "outputs": {}})
                self.assertEqual(run.started, {"select-source", "holbuild-success"})
                self.assertEqual(run.results["holbuild-success"], "failure")


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
        jobs = {name for name, job in self.jobs.items() if "environment" in job}
        self.assertEqual(jobs, CACHE_JOBS)
        for name in sorted(jobs):
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
        github = {"run_id": 42, "run_attempt": 1, "sha": MAIN_SHA}
        approved = render(command, github=github, needs=APPROVED, steps=steps)
        self.assertIn(f"snapshot-key=holbuild-v3-stage-T-build-{FORK_SHA}-42-1", approved)
        ordinary = render(command, github=github, needs=ORDINARY, steps=steps)
        self.assertIn(f"snapshot-key=holbuild-v3-build-T-{MAIN_SHA}-42-1", ordinary)

    def test_artefact_names_the_selected_sha(self) -> None:
        name = step(self.jobs["build-rollup"], name="Upload HBX artefact")["with"]["name"]
        name = name.replace("${{ env.HBX_BASENAME }}", "vyper-hol")
        github = {"sha": MAIN_SHA}
        self.assertEqual(render(name, github=github, needs=APPROVED), f"vyper-hol-hbx-{FORK_SHA}")
        self.assertEqual(render(name, github=github, needs=ORDINARY), f"vyper-hol-hbx-{MAIN_SHA}")


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
                    # Empty outputs of a skipped select-source leave
                    # checkout's own default: the triggering ref and commit.
                    self.assertEqual(s["with"], {
                        "repository": "${{ needs.select-source.outputs.repository }}",
                        "ref": "${{ needs.select-source.outputs.sha }}",
                        "persist-credentials": "false",
                    })
        self.assertEqual(checkouts, CACHE_JOBS | {"python-o1-oracle", "export-vyper-tests"})

    def test_selector_has_no_secrets(self) -> None:
        selector = self.jobs["select-source"]
        self.assertNotIn("environment", selector)
        self.assertNotIn("needs", selector)
        self.assertEqual(selector["permissions"], {"contents": "read", "pull-requests": "read"})
        self.assertEqual(self.workflow["permissions"], {"contents": "read"})
        self.assertEqual(set(self.workflow["on"]), {
            "workflow_dispatch", "schedule", "pull_request", "merge_group", "push",
        })

    def test_every_job_needs_the_selector(self) -> None:
        for name, job in self.jobs.items():
            if name not in ("select-source", "tested"):
                with self.subTest(job=name):
                    self.assertIn("select-source", job["needs"])

    def test_snapshot_keys_name_the_selected_sha(self) -> None:
        for name in ("toolchain", "build", "compiler", "test-deps"):
            with self.subTest(job=name):
                command = step(self.jobs[name], id="cache-key")["run"]
                self.assertIn("-${{ needs.select-source.outputs.sha || github.sha }}-${{ github.run_id }}", command)
        rollup = step(self.jobs["build-rollup"], name="Save holbuild project snapshot")
        self.assertEqual(rollup["with"]["key"], "${{ needs.build.outputs.holbuild-cache-key }}-rollup")

    def test_only_the_ordinary_build_snapshot_uses_the_restore_prefix(self) -> None:
        self.assertEqual(WORKFLOW.read_text().count("outputs.build-prefix"), 1)
        self.assertIn("outputs.build-prefix", step(self.jobs["build"], id="cache-key")["run"])
        toolchain_save = step(self.jobs["build"], name="Save holbuild toolchain cache")
        self.assertEqual(toolchain_save["if"], "${{ github.event_name == 'push' }}")

    def test_success_check_needs_every_job(self) -> None:
        self.assertEqual(set(self.jobs["holbuild-success"]["needs"]), set(self.jobs) - {"holbuild-success"})


@unittest.skipUnless(JQ, "needs jq on PATH")
class TestReleaseRunChoice(unittest.TestCase):
    """The release takes the newest successful holbuild run of its commit that is not an approved PR run."""

    @classmethod
    def setUpClass(cls) -> None:
        find = step(load_workflow("release.yml")["jobs"]["promote-hbx"], name="Find matching holbuild run")
        cls.filter = find["env"]["LATEST_RELEASE_RUN"]

    def choose(self, runs: list[dict[str, Any]]) -> str:
        """The run id the filter picks from `runs`, newest first."""
        result = subprocess.run([JQ, "-r", self.filter], input=json.dumps(runs), text=True,
                                capture_output=True, check=True)
        return result.stdout.strip()

    def test_approved_runs_are_passed_over(self) -> None:
        runs = [
            {"databaseId": 3, "event": "workflow_dispatch", "displayTitle": f"Approved PR 758 at {FORK_SHA}"},
            {"databaseId": 2, "event": "workflow_dispatch", "displayTitle": "holbuild"},
            {"databaseId": 1, "event": "push", "displayTitle": "Merge pull request #757"},
        ]
        self.assertEqual(self.choose(runs), "2")
        self.assertEqual(self.choose(runs[:1]), "")

    def test_push_and_merge_group_runs_are_kept_whatever_their_title(self) -> None:
        for event in ("push", "merge_group"):
            with self.subTest(event=event):
                runs = [{"databaseId": 5, "event": event, "displayTitle": "Approved PR handling"}]
                self.assertEqual(self.choose(runs), "5")


if __name__ == "__main__":
    unittest.main()
