# Milestone 1 maintainer reports

Prepared **2026-10-09** (host `date -Iseconds`), against accepted TASK057
`e88dae75fcc7b5fe05ceef26bb07aa493ecee2c9`, whose semantic baseline is
`e4cb0914`. **Submission-ready LOCAL reports only; nothing submitted externally.**

## Reports

The identifiers are the official PLAN identifiers, not shorthand task labels.
In particular F18 is ranges, F21 is source memory/name allocation, F22 is the
unsupported lowering catalogue, F23 is STOP, and F24 is empty INVOKE arguments.
ABI ensure belongs to F16; STOP/remap and token/FMP cross-references in F21/F22
are related evidence, not a renumbering. F17 dynamic decoding and F25 DFT are
outside this twelve-report ownership.

| Finding | Intended subsystem | Current disposition |
|---|---|---|
| [F10](F10-invalid-ec-points.md) | Source EC builtins | FIXED here, TASK007 |
| [F11](F11-storage-pop.md) | Source storage/transient arrays | FIXED here, TASK008 |
| [F12](F12-empty-account-codehash.md) | Source account operations | FIXED here, TASK009 |
| [F13](F13-conversions.md) | Source conversions and typing | FIXED here, TASK010–013 |
| [F14](F14-unsafe-div-zero.md) | Source integer arithmetic | FIXED here, TASK014 |
| [F15](F15-decimal-minimum-mul.md) | Source decimal arithmetic/type bridge | FIXED here, TASK015 |
| [F16](F16-fixture-typing-abi-encode.md) | Source checker / ABI builtins | FIXED here, TASK011/012/016 |
| [F18](F18-literal-range-bounds.md) | Lowering / frontend fixture ASTs | FIXED here, TASK017 |
| [F21](F21-fixed-memory-and-names.md) | Lowering allocations and namespaces | BOUNDED by SUPPORTED whitelist; general repair DEFERRED |
| [F22](F22-outside-supported-lowering.md) | Lowering expressions/statements/ABI/events | BOUNDED by SUPPORTED whitelist; general repair DEFERRED |
| [F23](F23-stop-returndata.md) | Venom halt semantics / codegen | FIXED here, TASK023; dynamic decode is NOT fixed |
| [F24](F24-empty-invoke-arguments.md) | Venom function entry / unit shape | FIXED here, TASK024; stage simulations remain ADMITTED |

## Reading and static reproduction

Each report gives literal inputs, old source versus target results, current
source/theorem names and pinned reference Python functions. These are
**definition-level counterexamples unless expressly identified as historical
rebuilt regressions**. A theorem declaration in current Git is not a new saved
kernel-object check. This task read sources and existing receipts, parsed selected
JSON evidence, checked links and Git preservation, and made documentation only.
It ran **no HOL, tests, parity, generated suite, compiler, or audit tool**.

To reproduce the *inspection*, use the linked repository files at `e88dae75`;
for the original clauses use `git show c587772d:<linked-source-path>` (read-only).
Follow each named function and its constants with the supplied literal input.
Inspect the named regression's statement/proof and the receipt below; do not
interpret these instructions as a test executed by TASK059. Full compiled-run
claims require their own execution/proof evidence, not arithmetic inspection.

Reference access verified read-only: `/home/dev/vyper-hol/reference/vyper-src`,
Git **`cd74ce4f57e3771aeeab8f061fa3be45bfe8a29c`**, matching
[the pin](../../VYPER_PIN). `vyper-ref` is absent; no symlink/clone was created.
Report reference paths are relative to that checkout, with function names and
observed line ranges; no Python compilation was run. Export JSON lives at
`/home/dev/vyper-hol/reference/tests/vyper-test-exports` and was parsed as data
only, never evaluated. Selected `source_code` fields and trace keys were inspected:

| Export | Evidence inspected, not a fresh run | SHA256 |
|---|---|---|
| `functional/builtins/codegen/test_ec.json` | `test_ecadd`, deployment trace `source_code` contains `_ecadd(x: uint256[2], y: uint256[2])`; eight named EC items | `e1753c8bdb1314fdd1546d62ac0ef470b831e6405a87fe4e3132bf587d08f63c` |
| `functional/builtins/codegen/test_abi_encode.json` | `test_abi_encode`, deployment trace `source_code` contains Animal/Human struct encoders; not falsely identified as the separate ABI fixture | `2df06e5abe3c9d1bf126645d2ee306537acfafe616dce1180a86dddaef5576f8` |
| `functional/codegen/types/test_dynamic_array.json` | actual item/trace schema and original input hash, not an assertion all traces pop | `80c51b5ffb695a3b7c0c9a79b95f28f7cff1e3a59854806ec95a87de92da7f15` |

## Historical planning and proof history

Official planning input read in the coordinating worktree:
`/home/dev/vyper-hol/worktrees/milestone-1/.agent-files/PLAN.md`, written
2026-10-01 against **`c587772d`**, reference **`cd74ce4f`**. That separate ignored
records repository is not added here. Citations in reports identify exact PLAN
section/finding/decision and historical source lines; they do not transplant
old line numbers onto current files. TASK059 and `tasks/ACCEPTANCE.md` were also
read there: documentation/evidence gate only, no routine replay.

PLAN §10 T10 item 4 (T10.4), lines 3191–3194, calls for these twelve reports.
§4.2 covers F10–F16 (685–756); §4.3 F18/F21/F22 (778–847); §4.4 F23/F24
(849–865). §3 D9–D14/D19, §5.3 correction table (1327–1343), §5.6 exact
whitelist (1630–1740), and §6.2 comparisons (2483–2520) determine dispositions.
The implementation ledger `tasks/IMPLEMENTATION_NOTES.md` and reports008–024
were read, including superseding final013, final022 and primary016. Private
commit IDs in receipts differ from landed cherry-picks; reports cite **landed
Git IDs**, with receipt IDs labelled separately.

Durable navigation:
[original proof drafts and counterexamples](../compiler-proof-drafts-and-counterexamples.md),
[historical audit](../compiler-proof-status-2026-09-28.md),
[retired proof/API history](../../lowering/e2eLegacy.md),
[current dated audit](../compiler-proof-status-2026-10-09.md),
[current pointer](../compiler-proof-status.md),
[roadmap](../compiler-proof-roadmap.md).
The roadmap path exists now; TASK058 owns its update, not this task.
Historical audit/parity prose is not relabelled as current certification.

## Existing receipts and limits

Absolute `/tmp` receipts below were actually read and remain **ephemeral external
local evidence**, not portable repository artifacts. Durable witnesses are the
linked Git sources and commit identities. No receipt was manufactured/rebuilt.

| Findings | Receipt read | Recorded scope; not rerun here |
|---|---|---|
| F10 | `/tmp/m1-result-007.md` | 82 source/property targets, eight EC traces, seven added EC theorems; four no-TypeError claims preserved; original parity audit was tag/dependency-only, not a Hyp0 certificate |
| F11 | `/tmp/m1-result-008.md` | eight pop regressions; both storage backends retain 37 at slot6; full selected3820 historical source acceptance |
| F12 | `/tmp/m1-result-009.md` | eight codehash boundaries; 21 inspected closed source objects; explicitly94 historical conditional parity objects, NOT then closed certificates |
| F13 | `/tmp/m1-result-010.md`, `011.md`, `012.md`, `013-final.md` (same prefix) | corrected scalar boundaries/checker acceptance; 30/34/34/17 scoped objects; final013 supersedes incomplete013 |
| F14/F15/F16 | `/tmp/m1-result-014.md`, `015.md`, `016-local.md`, `016-primary.md` | LOCAL44/29/35 focused objects; primary016 at `707ec670`:170 source theories+5 libraries,254 generated owners,127 cohorts/3820 exact closed selected results. Local016's pending status is superseded only by that boundary |
| F18 | `/tmp/m1-result-017.md` | seven range/source regressions, five unchanged byte endpoints; tag-only historical parity evidence is not today's closure |
| F21/F22 | `/tmp/m1-result-018.md`, `019.md`, `020.md`, `021.md`, `022-final.md` | compiler budget; exact support boundary, NOT general semantic fixes; final022101 exact membership conclusions/plain EVAL; partial022 superseded |
| F23/F24 | `/tmp/m1-result-023.md`, `024.md` | three STOP and four empty-INVOKE regressions;024 honestly records203 inherited parity hypotheses at its revision |
| Related remap/shape | `/tmp/m1-result-061.md`, `043.md` | frozen original GETFMP witness/full existential negation; four-field contract repair; shape/L4 checks, not S2/S6 proof |
| Current classification | `/tmp/m1-result-056.md`, `057.md`, `/tmp/m1-task056-evidence.json` | exact accepted top/generic dependency classification and130→128 named site delta |

Selected machine-readable receipts parsed here: final013
`/tmp/m1-task-013-evidence/acceptance-summary.json` records421/68 targets,
3820 results,202 unchanged lists and preserved patch/statements; primary016
`/tmp/m1-primary-016/verification-summary.json` records the exact boundary above,
260 unchanged framework sources/252 export JSONs and **no parity**; TASK056 JSON
records130→128, no additions and top7/generic0. These are source/receipt checks,
not fresh kernel validation. This documentation commit changes no fixture AST,
plain-EVAL endpoint, source binary/hex list, frozen remap witness or proof text.

## Local documentation gate

The docs-only inspection passed: twelve reports plus this index, **155 local
links** resolved inside the assigned repository (no fragment links remain),
90 named current theorem/definition declarations located in25 source owners,
and36 pinned-reference class/function declarations in17 Python owners.
Python was used to parse text/AST/JSON only, never to import/run the reference
compiler. Git blob identities for **all1332 original tracked regular files**
matched the accepted base before commit; no source/proof/fixture/byte change.
Final commit's scope/cleanliness is recorded in `/tmp/m1-result-059.md`.

A portable link-only reinspection from the repository root is:

```sh
python3 - <<'PY'
from pathlib import Path
import re
root = Path.cwd().resolve()
files = sorted(Path('docs/findings').glob('*.md'))
assert len(files) == 13
links = 0
for doc in files:
    for url in re.findall(r'\[[^\]]+\]\(([^)]+)\)', doc.read_text()):
        assert '://' not in url and '#' not in url, (doc, url)
        target = (doc.parent / url).resolve()
        assert target.is_relative_to(root) and target.exists(), (doc, url)
        links += 1
print(len(files) - 1, 'reports + index;', links, 'resolved local links')
PY
```

This is a static documentation gate, **not** a HOL/suite/audit-tool invocation.
For the original TASK059 delivery, inspect
`git diff ceae858c 0c622fda --name-status`: exactly these13 new Markdown files
appear. Later TASK060 documentation updates are separately recorded. For theorem evidence follow each named source and
receipt above; declaration parsing alone does not verify a saved kernel object.

**Full-site classification remains the TASK057 audit's128 live source sites;
the current top has exactly seven ADMITTED leaves S1–S7, generic composition
has zero.** Off-path deployment and function simulation are separately admitted.
The original reports' sourced classification is **not a fresh certificate**.
The subsequent [TASK060 exit verification](../compiler-proof-milestone-1-exit-2026-10-09.md)
passed final merged default/optional closure, all3820 selected results, all101
memberships, strict101 certificates/202 independent unchanged byte lists and
final dependency/admission/documentation checks. This does not turn whitelist
membership, corrections or admitted stages into a fully verified compiler.
