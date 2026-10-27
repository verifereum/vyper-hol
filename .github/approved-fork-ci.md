# Maintainer-approved fork CI

## Problem

A pull request from a fork runs no `holbuild` jobs: PR runs get the remote
cache login, which can write cache entries, so only branches of this
repository, which need write access to push, are trusted with it. The merge
queue tests fork PRs before they land, but their authors get no CI result
until then. A maintainer can run the full cached CI on a reviewed fork PR
head by dispatching `holbuild` on `main`.

## Usage

```sh
gh workflow run holbuild.yml --repo verifereum/vyper-hol --ref main \
  -f pr_number=758 -f approved_sha=FULL_REVIEWED_HEAD_SHA
```

Replace the example number and SHA with the PR and its reviewed, full
40-character lowercase head SHA. Both inputs must be given together, and
`uncached` must stay off: an approved run exists to use the remote cache
login, which `uncached` withholds. Leaving both PR inputs blank keeps an
ordinary manual run. The workflow must be on `main` before this entry point
is available.

The approved commit must be up to date with `main`'s CI: the jobs come from
`main`'s workflow and call the local actions and `tools/` scripts of the
checked-out commit, so a head based on an older `main` may lack them.

## Trust

Approval gives the selected code the remote cache login, and the Actions
cache scope of `main`, which every branch and PR restores from. Review its
local actions, build scripts and dependencies as well as its proofs: all of
them run with that trust. The workflow's own cache keys keep an honest
commit's project state out of other runs (see Caches), but the commit's
local actions can save any cache key they choose. No automatic fork trigger
or token write permission is added.

## Validation

The `select-source` job runs first, with no checkout and no cache login. On
an approval it checks that the dispatch is on `main`, that the PR is open,
targets this repository's `main`, and still has exactly the approved head
SHA. Every job that checks out code waits for it and checks out the
repository and immutable SHA it returns, with checkout credential
persistence disabled. A later push cannot change the checked-out source; a
run for the new head needs a fresh approval. If the PR moves before
validation, validation fails. On any other event `select-source` returns
the triggering commit and grants nothing.

## Jobs

The job definitions come from `main`; changes to the approved commit's
workflow YAML are not used. The approved run is the ordinary graph at that
commit: `toolchain`, `build`, `compiler`, the witness groups,
`build-rollup`, `test-deps`, `python-o1-oracle`, `export-vyper-tests` and
the test groups. `tested` runs only on pushes, so the tests are never
skipped. Every cache-using job gets the cache login through the
`bazel-cache` environment, which admits the run because it is on `main`.
`holbuild-success` also requires `select-source` to succeed, so a rejected
approval fails the run.

## Caches

An approved run restores `main`'s latest project snapshot, as a PR run
does. A PR run's saves stay in the PR's own cache scope; an approved run's
land in `main`'s, so its project snapshots (`build` and `build-rollup`) are
saved under the stage prefix, whose exact keys only this run restores,
instead of the build prefix every run restores from. The Poly/ML, holbuild
and Vyper test export caches keep their keys: each names the pinned inputs
it is built from, so on a miss the run saves what any run would build.

## Identification

The run title (`Approved PR <n> at <sha>`), the `select-source` summary,
every snapshot key and the HBX artefact (`vyper-hol-hbx-<sha>`) name the
approved SHA. Each approved run has its own concurrency group, so
approvals do not cancel one another. The run belongs to the dispatch on
`main`: it attaches no check to the PR and does not move the merge queue.

`release.yml` promotes the HBX of the latest successful `holbuild` run of
the release commit. An approved run's commit is the `main` commit it was
dispatched on, but its artefact is named after the approved SHA, so it is
never promoted; if it is that latest run, the release fails to find the
artefact, and an ordinary run of the release commit is needed.

## Local checks

The selector and job wiring are checked with PyYAML, and with Node on
`PATH` for the selector script and expressions:

```sh
cd tools && python3 -m unittest -q test_approved_fork_ci
actionlint .github/workflows/holbuild.yml
```
