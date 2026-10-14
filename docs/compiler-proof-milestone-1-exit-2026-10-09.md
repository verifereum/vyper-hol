# Milestone 1 exit verification — 2026-10-09

**Milestone 1 is complete. This is not a fully verified compiler.**
The runtime theorem still depends on exactly the seven explicitly admitted
stages S1–S7. Generic composition and L1–L13 are admission-free. Function and
deployment simulation remain separately admitted, off the runtime call path.
Environmental producers and combined boundary satisfiability remain future work.

## Certified identity

- Combined PRIMARY revision: `0c622fda333f3c324010a9980c264a89ea6d4023`.
- Last SML revision: `e4cb09143b677747c4f857185e515b9c5999fe0c`.
- SHA256 of the complete 1,045-file SML/signature identity map:
  `eb498134563704e212038f553f307d809641f78230e27ee918c8fa1b33438aed`.
- Verifereum: `b116b3c46c17381e968d25b81cd81b6ab2b76ab2`; source identity digest
  `6e4b83bbcad6f15559ce642c88360fcada000bf242635ca437c908d563c67a4f`.
- Config SHA256: `holproject.toml`
  `9fb0b52ae438faad6a994ee72e4839a54a040e275dbaab04854140b52ec2ba32`;
  `.holconfig.toml`
  `102227c4bb6669d17933346279fa400b50fab9c84abdb77b93f28cc92c2e69b2`;
  `VYPER_PIN`
  `9a123fbe3fda20b7ef84343203c21043151277d7175e47ecdc9ec774bf6a6b68`.

This exit-document commit changes documentation only. It does not change any
certified source, dependency, configuration, fixture or oracle identity.

## Executed final checkpoint

All **28 build operations and four saved-kernel audits exited 0**, using
normal caches/checkpoints, one foreground build at a time, heap 16,384 and
`-j1`. Ordinary tactics were limited to 10 seconds. The previously authorized
bytecode-specific 600-second exception was used only for mandatory final parity
and its strict audit, after current ordinary-10 prerequisites passed.

| Operation | Explicit roots / scope | Accepted receipt |
|---|---|---|
| Ordinary batches | 738 roots, batches 000–023 | `execute-000` … `execute-023` |
| Generated suite | 254 theories | `execute-024` |
| Complete non-parity union | 992 roots | `execute-025` |
| Mandatory final parity | 46 exclusive parity/reverse-closure roots | `execute-026-final` |
| Configured defaults | Four explicit roots, tactic 10 | `execute-027` |
| Generated/source/changed/strict kernel audits | Four external audit roots with PRIMARY disk override | `generated-kernel`, `source-kernel`, `changed-kernel`, `strict-kernel` |

The full scope includes all 1,017 theory roots, 20 structured SML modules and
tracked raw `test_bridge` compilation. The raw file was not misrepresented as a
saved-theorem certificate. Default roots were `vyperHolTheory`,
`vyperCheckContractLibTestTheory`, `vyperCheckContractFrontendLibTestTheory` and
`vyperCheckContractTraceLibTestTheory`; their closures contain no parity roots.
Every actual transitive plan was reviewed before execution.

Two parity attempts reached their bounded 3,600-second aggregate deadlines.
Their completed leaves were reused normally; the third bounded attempt passed.
Failed/interrupted attempts are retained and are **not** successful evidence.
No production source repair, skipped goal feedback, cache bypass, copied live
objects, forced cold replay or fixture/oracle change was needed.

## Saved objects, independent bytes and coverage

- **3,820** exact selected closed generated results in the original **127**
  cohorts; **252** input JSON identities and raw coverage unchanged.
- **101** exact supported-program membership exports, each plain `EVAL_TAC`.
- **101** original full compiler equalities, each plain `EVAL_TAC`, with empty
  kernel hypotheses, no axioms and no admission tags.
- **202** independently Python-decoded deployment/runtime lists compared with
  the actual saved theorem RHS: all **44,632 bytes unchanged**.
- **826** evaluation and **394** support exports rechecked clean.
- **1,451** clean source selections and **497** clean changed/focused selections;
  ten admitted objects classified separately, never certified clean.
- TASK034's four restored oracle-state claims and eight CV owner relocations
  remain checked. Seven explicitly retired compatibility entries have documented
  current replacements, not asserted old/new equivalence.
- TASK065's 265 cohort files retain 264 byte-identical files; the sole accepted
  TASK027 source helper migration adds the explicit `NONE` argument. The
  compiler fixtures, plain-EVAL endpoints and independent oracles are unchanged.

## Every PLAN §12 exit item

| Requirement | Verified evidence |
|---|---|
| DEAD/superseded FALSE admissions retired | Named site ledger and clean source/changed audits; original proof provenance retained. |
| Frame-aware top, no old run-based compatibility boundary | Exact saved §2.1 schema in `e2eCallChecks`; `call_result_rel` uses `frame_outcome` and Verifereum `run_call`. |
| Non-vacuous gas clause | Actual frame OutOfGas/StackOverflow or valid computed-precompile failure, not an unconditional gas escape. |
| D12–D14 corrections and proof preservation | Complete source/CPS/CV/small-step, Venom/assembly/pass/codegen closure and exact regressions; 15,767 same-owner proof comparisons found no formerly proved semantic claim newly cheated. |
| 101 memberships and original plain-EVAL parities | Exact manifest bijections, saved hypotheses/tags and independent byte audit above. |
| Final named stage statements | S1–S7 saved and explicitly classified ADMITTED. |
| Identity finalizer and runtime assembly | `K SOME`; clean L1 proves `runtime_bc = assemble prog`; no active `finalizer_correct`. |
| Old premises eliminated/produced; exactly seven path admissions | Exact public schema, named L1–L13 and built dependency audits. |
| Meaningful deployment | Exact §5.11 singleton creation/code-installation statement, separately admitted; old vacuous placeholder/proof retained as provenance. |
| Dated complete assumption audit and handoffs | [Status](compiler-proof-status-2026-10-09.md), [dependencies](compiler-proof-dependencies.md), [specification](compiler-correctness-specification.md#calls-and-nested-contexts), [roadmap](compiler-proof-roadmap.md) and [twelve local finding reports](findings/README.md). |
| Full builds and 128 named sites | All operations/audits above; unchanged `cheat_audit.py sites`, `dependents`, `deps` and independent tracked/untracked-source scan. |

Final **128** site identities are baseline 136 minus **15 named removals** plus
**seven planned additions**, not a count-forcing deletion. TASK056 separately
removed the temporary correspondence and legacy-codegen admissions, 130→128.
The [retirement ledger](../lowering/e2eLegacy.md) records all 21 obsolete
definitions and 14 claim/helper entries, original proofs and replacements.

The top's exact admitted leaves are:

1. `vyperLoweringCorrect.lower_vyper_runtime_unit_correct` — S1
2. `vyperLoweringCorrect.lower_vyper_runtime_unit_source_unit_ok` — S2
3. `vyperLoweringCorrect.lower_vyper_runtime_unit_memory_ok` — S3
4. `o1PipelineCorrect.run_venom_pipeline_correct` — S4
5. `o1PipelineCorrect.o1_pipeline_memory_obligations` — S5
6. `o1PipelineCorrect.run_venom_pipeline_output_shape` — S6
7. `codegenCorrectness.codegen_correct` — S7

Generic `e2e_vyper_to_evm` and each L1–L13 have **zero** admitted dependencies.
Neither deployment nor `gen_fn_simulation` nor a legacy bridge is on this path.

## Checkpoints, provenance and limits

Historical combined-primary checkpoints TASK016 (`707ec670`), TASK034
(`ace9f467`) and corrected TASK042 (`f0d91005`) remain preserved. TASK060
validated their current affected closures/results rather than promoting
source-only historical reuse candidates to cache/kernel certificates. TASK042's
initial erroneous parity-overlap attempt is excluded from acceptance.

External receipts are retained at
`/tmp/m1-evidence-060-prep/final-combined-03/`; reports are
`/tmp/m1-result-060-primary.md` and `/tmp/m1-exit-060-primary.json`. These are
**ephemeral external artifacts**, not promised permanent repository links.
Their durable digest inventory is [the exit certificate](compiler-proof-milestone-1-exit-2026-10-09.json).
The manifest records exact source/dependency/target identities; each receipt
records commands, expanded plans, input keys, output metadata and logs. The
complete verifier, final reconciliation and actual checker transcripts passed.

No remaining Milestone 1 task-induced repair or checkpoint debt exists.
Future work remains exactly as classified: stage proofs, function/deployment
simulation and environmental/callee producers and satisfiability. This result
provides no universal compile-success, whole-transaction, fallback/static-entry,
runtime-immutable, `msg.gas`, sufficient-gas or general revert-data guarantee.
Success alone compares requests; terminal leftover outcomes are not observables.
The dynamic-decoding exemption remains the exact documented
`RuntimeError "abi_decode invalid"` case, not arbitrary decoding failure.
