# Nested-place regression inputs and validation

`sources/` contains the 69 supplied witnesses and fixture aliases. Preparation
reads these checked-in files; it does not regenerate source templates.
`source-audit.json` records their hashes and the token comparison with TASK.
They remain separate from the frozen 101-fixture corpus.

`recovery-manifest.json` identifies the original producer, revision, retained
archives and public evidence. The historical E0018 matrix reported 60 MATCH,
seven PARITY_DEFECT and two NONE results. These are historical observations,
not a claim that the current matrix passes. The historical plus-assignment
version of `g5_hm_nested_aug` is preserved in that archive; the checked-in TASK
witness uses subtraction.

## Reproducible checks

Run from the repository root:

```sh
holbuild nestedPlaceSupportTheory
holbuild nestedPlaceValidationTheory
holbuild nestedPlaceS20Theory
holbuild nestedPlaceMatrixTheory
```

The support target checks both checker modes and saves a kernel theorem for
each source's `supported_program` verdict. Its explicit exclusions retain
independent storage decoding, aggregate copy, Append/For, immutable and internal
return restrictions. A rejected support verdict does not itself establish a
bytecode defect.

The validation target covers the twelve entries in `parity-fixtures.txt`.
The strict S20 target requires checker acceptance and exact deployment/runtime
bytecode equality. The matrix target retains all 69 per-stage observations in
`matrix.tar.gz`, including checker failures, NONE and residual results. Inspect
`actual/status.json`; a successful diagnostic build or archive alone is not a
parity certificate. The support target publishes `support.tsv` separately.

These actions are opt-in and explicitly impure. They invoke the pinned Vyper
compiler independently and never recursively invoke holbuild. Preparation
defaults to the existing environment at
`/home/lukasz/.local/share/uv/tools/vyper/bin/python3`; `NESTED_PLACE_PYTHON`
overrides it. `oracle/provenance.json` records compiler settings and provenance.

## Independent EVM behaviour

Use an existing environment with py-evm, eth-abi, eth-keys and eth-utils:

```sh
python lowering/defs/bytecode/nested_place_execute.py \
  --matrix lowering/defs/bytecode/nested-places/matrix.tar.gz \
  --all --report lowering/defs/bytecode/nested-places/behaviour-all.json
```

The driver runs signed Prague transactions against both runtimes, checks
literal return/storage expectations, exercises bounds and rollback, and checks
transient cleanup across transactions. Full coverage seeds different struct
fields with different values, checks structured ABI returns, calls the setter
before the storage-field iteration witness, and executes deployment for the
immutable witness. Expected behaviours are independent of HOL output.

Pending dependency failures are reported as DEFERRED only for the named HOL
witnesses when both the compiler stage and observed error match the retained
failure. They retain that error and prerequisite. Vyper failures and
unconditional HOL failures remain errors. `--case NAME` selects one of the
original expanded behaviour cases; `--diagnostics` selects the corrected-source
subset. `--all` covers every supplied source and cannot be combined with those
filters. The report distinguishes PASS and DEFERRED; inspect both.

Generated oracle files, HOL outputs, archives and reports are ignored. Preserve
them with hashes when recording validation evidence, including failures.

## Current witness results

`validation-results.json` records the verified 69-source matrix: every source
is accepted in both checker modes, 62 have identical deployment and runtime
bytes, five retain parity differences, and two return NONE. The independent
execution report contains 69 Vyper passes, 62 HOL passes and seven explicit HOL
deferrals. The support audit admits 55 sources and retains 14 independent guards.

The primary-baseline witness prerequisites are:

| Witness | Observed result | Prerequisite |
| --- | --- | --- |
| `f32_for_storage_struct_field_arr` | PARITY_DEFECT | #559 storage-field iteration |
| `f38_for_storage_struct_field_arr_set` | PARITY_DEFECT | #559 storage-field iteration |
| `g2_a_dyn_nested` | PARITY_DEFECT | #559/#560 nested Append and copy |
| `g3_st_dyn_field` | PARITY_DEFECT | #559 attribute Append |
| `s16_storage_map_of_dynarray_elem` | PARITY_DEFECT | #559 subscript Append |
| `m10_imm_nested_array` | NONE | #563 immutable aggregates |
| `p57_int_struct_local_return` | NONE | #545 internal struct returns |

Supplemental validation with the #563/#545 implementations now verifies m10
and p57: both checker modes accept them, deployment/runtime bytes match both
fresh and retained pinned oracles, and all four Vyper/HOL EVM rows pass.
m10 is actually deployed before `get(1)` returns 4; p57's `foo(9)` returns 7.
The isolated composition and its source/output hashes are retained in
`.agent-files/recovery/diagnostic/conditional-m10-p57-complete-20261026T220653Z.json`
(archive SHA256 `0e661e140b80a21320f3fe7ac35d3452ac11237f756134c13e2d95f3e664fbe1`).
This leaves five unresolved witness prerequisites. The baseline matrix and
support verdicts above retain their original results.

A public HTTPS check on 2026-10-28 verified that [#559 remains open](https://github.com/verifereum/vyper-hol/issues/559)
and [#560 is closed](https://github.com/verifereum/vyper-hol/issues/560).
Upstream main `04250b7f` still uses the legacy root-based For/Append paths.
All five unresolved cases need #559; #560 is not independently unavailable.
The exact lookup and source observations are retained in
`.agent-files/recovery/diagnostic/remaining-dependency-lookup.json`.

All twelve requested fixture families are present in `parity-fixtures.txt`.
`diagnostic-results.json` preserves an earlier diagnostic run; its S20 parity
difference predates the DFT repair. The current S20 source matches and returns
5 with counter 11 in both runtimes.

The original 101-fixture corpus is a separate completion gate:

```sh
holbuild --maxheap 8192 -j 1 build evalCompilerBytecodeParityTheory
```

Development and focused rechecks retain normal caching and checkpoints.
After the incremental aggregate passes, final validation uses:

```sh
holbuild --maxheap 8192 -j 1 build --force=theory --no-cache --skip-checkpoints evalCompilerBytecodeParityTheory
```

This reruns the aggregate's inspection of all 101 saved theorem objects against
the dependencies validated by the preceding incremental build.

Its audit requires the exact 101 qualified public theorem names, zero kernel
hypotheses, no axioms and only ordinary DISK_THM storage tags. The 33 oracle
reader scripts declare their exact 101 hex inputs. The six pure stage scripts
use their logical dependencies without copying the oracle directory. The
core integration passed all fourteen targets. Direct kernel checks also passed
for five changed monotonicity helpers and both place callback contracts.
`normal-corpus-fidelity.json` in the retained diagnostic evidence records that
the exact original 101 public identities, 109 input-theory definitions and all
101 oracle files are preserved against revision `0273aab9`.
Those definitions comprise 101 programs and eight program-building helpers.

The cold ABI resource test passed all 495 availability checks and the original
public bytecode equality with checkpoint reuse and saving disabled, at the
normal 2.5-second tactic limit. Its complete logs and sixteen proof source files
are preserved in `abi-cold-complete.tar.gz` in the retained diagnostic evidence,
with the exact command and digest in `abi-cold-complete.json`. Shared named
query inputs reduced the exported analysis from 261.5 MB to 10.2 MB; each of
the thirteen availability slices completed in under 20 seconds.

All 33 public component theories passed their incremental builds. The normal
aggregate then passed the exact original 101-theorem kernel audit: zero
hypotheses, no axioms, and only DISK_THM storage tags, with no CHEAT warnings.
Caching and checkpoints remained enabled throughout development. The normal
aggregate receipt and focused source/log/export receipts are recorded in
`validation-results.json`.

The type-builtin, width, state-access and baseline fixtures retain every
original theorem statement and EVAL_TAC proof body. A shared helper derives
checked compiler-boundary equations before those proofs; it reads no oracle
bytes. The existing unary fixture supplied the staging pattern.
The conditional m10/p57 probe passed byte equality and all four EVM rows in
an isolated composition with the #563/#545 implementations.
The final forced aggregate audit also passed all 101 kernel checks with caching
and checkpoint saving disabled. It inspected the saved theorem objects against
the dependencies validated by the incremental build; it did not rebuild every
dependency from scratch. Commands, source and evidence digests are recorded in
`validation-results.json`. All original statements, inputs and oracle bytes
are preserved.

Issue #558 is complete. As explicitly required by the task and confirmed by
the user, the For/Append/Pop migration remains with #559. Its five dependent
witnesses retain their observed PARITY_DEFECT results as external deferrals;
they are not blockers for completing #558 and are not relabelled MATCH.
`task_complete` is true for issue #558 only. The scope correction is recorded
in `.agent-files/recovery/diagnostic/issue558-completion.json`; the earlier
immutable validation bundle retains its historical completion classification.
