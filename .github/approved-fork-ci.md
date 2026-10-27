# Maintainer-approved fork CI

Ordinary fork pull-request runs cannot use the remote cache login. A
maintainer with repository write access can explicitly approve a particular
PR head commit for a cached run by dispatching `holbuild` on `main`:

```sh
gh workflow run holbuild.yml --repo verifereum/vyper-hol --ref main \
  -f pr_number=758 -f approved_sha=FULL_REVIEWED_HEAD_SHA
```

Replace the example number and SHA with the PR and its reviewed, full
40-character lowercase head SHA. Both inputs must be supplied together.
Leaving both blank retains an ordinary manual main run without PR cache
approval. The workflow must be merged to `main` before this entry point is
available.

Approval grants the selected code access to the cache credentials in the
build and test jobs. Review its local actions, build scripts and dependencies
as well as its proofs: all execute with that trust. No new automatic fork
trigger or token write permission is added.

Before any candidate code runs, a job without cache secrets verifies that
the PR is open, targets this repository's `main`, and still has exactly the
approved head SHA. All checkouts use the returned repository and immutable
SHA with checkout credential persistence disabled. A later push cannot
change the checked-out source; a new run for that push needs fresh explicit
approval. If the PR moves before validation, validation fails instead.

The workflow and job definitions come from `main`. The selected commit
supplies the code and local actions; changes to its workflow YAML do not
replace the trusted job definitions. The existing build, Python oracle,
test-export and ten test-shard jobs still run, with the existing final
success check also requiring source validation to succeed.

The run title and source-selection summary identify the approved SHA.
Project snapshot cache keys and HBX artifact names use the selected SHA,
while shared toolchain and export caches keep their existing compatibility
keys. The Actions run belongs to the dispatch on `main`; it does not attach
a successful pull-request check or move the merge queue past its checks.

The selector and job data flow can be checked locally with Node and PyYAML:

```sh
python3 -m unittest discover -s tools -p test_approved_fork_ci.py
actionlint .github/workflows/holbuild.yml
```
