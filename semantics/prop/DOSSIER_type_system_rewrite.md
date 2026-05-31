# DOSSIER: type_system_rewrite

PLAN: `semantics/prop/PLAN_type_system_rewrite.md`

## Component Index

| Component | Status | Diagnosis | Latest Episode | Next |
|---|---|---|---|---|
| C0 | proved |  | E0001 |  |
| C1.1 | stuck | risk_mismatch | E0002 | Ask strategist to replace/augment C1.1 with an explicit standalone `extcall_expr_sound` theorem statement copied from the live generated-IH context, plus a small tail bridge helper if needed. |
| C1.1.1 | proved |  | E0004 |  |
| C1.1.2 | stuck | risk_mismatch | E0006 | Call plan_oracle review for C1.1.2 with the failure evidence; request decomposition around a smaller tail/evaluator-prefix boundary or permission to revert the partial helper. |
| C1.1.2.0 | proved |  | E0007 |  |
| C1.1.2.1 | proved |  | E0008 | Call plan_oracle review for C1.1.2.1, then if accepted commit the source checkpoint without GPG signing before beginning C1.1.2.2. |

## C0

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0001`
- blocker: 
- actual effort: 1 sessions, 1 steps, 138,836 tok (138,607 in, 229 out, 137,600 cached), 8.1s, $0.080705

### Attempts / Evidence

- `E0001` (proved, , actual effort: 1 sessions, 1 steps, 138,836 tok (138,607 in, 229 out, 137,600 cached), 8.1s, $0.080705)
  - Carry-forward baseline component begun to satisfy schedule gate; no source proof work authorized or performed under C0. -> C0 has no executor work; current actionable proof frontier is C1.1 per structured plan. ()

### Evidence refs

- `TO_type_system_rewrite-20260531T201607Z_m0023_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260531T201607Z_m0025_t001` (use `read_tool_output` for exact output)

## C1.1

### Current Status

- result: `stuck`
- diagnosis: `risk_mismatch` Not a theorem falsehood; this is a proof-interface/decomposition mismatch caused by trying the wrong inline proof shape. The next plan should force a standalone helper with a concrete statement matching the live generated IH context.
- latest episode: `E0002`
- blocker: The active C1.1 PLAN says the proof should be entirely helper-shaped and straightforward, but inline execution immediately creates timeout-prone >4KB goals. Continuing tactical repairs inside the Resume risks more thrashing; the component needs strategist review/recommitment to a precise helper statement/proof boundary or permission to replace the current inline attempt.
- actual effort: 1 sessions, 1 msgs, 11 steps, 10 tools, 3 holbuild, 1,604,921 tok (1,602,110 in, 2,811 out, 1,579,136 cached), 124.9s, $0.988768
- next: Ask strategist to replace/augment C1.1 with an explicit standalone `extcall_expr_sound` theorem statement copied from the live generated-IH context, plus a small tail bridge helper if needed.

### Attempts / Evidence

- `E0002` (stuck, risk_mismatch, actual effort: 1 sessions, 1 msgs, 11 steps, 10 tools, 3 holbuild, 1,604,921 tok (1,602,110 in, 2,811 out, 1,579,136 cached), 124.9s, $0.988768)
  - Tried proving ExtCall inline in the `Resume` by unfolding `evaluate_def`, splitting args success, then static/nonstatic and stepping monadic operations toward `extcall_return_tail_sound`. -> This violated the PLAN's helper-boundary guidance and produced repeated >4KB goals/timeouts on broad simplification (`gvs[]`, `simp[dest_AddressV_def]`) even for small list/case steps. Source was reverted to the original `cheat` so `vyperTypeStmtSoundnessTheory` builds again (with cheat warnings). (`TO_type_system_rewrite-20260531T201026Z_m0010_t001`, `TO_type_system_rewrite-20260531T201607Z_m0030_t001`, `TO_type_system_rewrite-20260531T201607Z_m0034_t001`, `TO_type_system_rewrite-20260531T201607Z_m0038_t001`)
  - Used `FAIL_TAC "probe_extcall_resume"` to inspect live ExtCall Resume context after `rpt gen_tac >> strip_tac`. -> The live context has a generated IH for args and an optional driver IH, plus a large evaluator-success implication already in assumptions. This confirms the proof should be factored into a standalone helper instead of continuing inside the Resume. (`TO_type_system_rewrite-20260531T201026Z_m0007_t001`)

### Ruled Out

- Do not continue inline `Resume` proof with broad `gvs[]`/`simp[]` after case splits; it repeatedly times out on large goals.
- Do not unfold all monadic definitions at once.

### Evidence refs

- `TO_type_system_rewrite-20260531T201026Z_m0007_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260531T201026Z_m0010_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260531T201607Z_m0030_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260531T201607Z_m0034_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260531T201607Z_m0038_t001` (use `read_tool_output` for exact output)

## C1.1.1

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0004`
- blocker: 
- actual effort: 1 sessions, 5 steps, 4 tools, 2 holbuild, 448,149 tok (446,738 in, 1,411 out, 439,168 cached), 142.5s, $0.299764

### Attempts / Evidence

- `E0003` (stuck, wrong_statement, actual effort: 1 sessions, 2 msgs, 10 steps, 15 tools, 3 holbuild, 750,395 tok (744,790 in, 5,605 out, 698,112 cached), 163.1s, $0.750596)
  - Inserted the PLAN-specified `extcall_after_state_update_tail_sound[local]` with `Call loc (ExtCall stat (func_name,arg_types,ret_type))` conclusion and tried the intended composition: derive runtime consistency by `update_accounts_transient_runtime_consistent`, then `irule extcall_return_tail_sound >> simp[]`. -> The proof reduced to unprovable side conditions including `∀e. drv = SOME e ⇒ ret_type = loc` and `∃ret_tv. evaluate_type env.type_defs loc = SOME ret_tv`, showing the wrapper statement is too general for the existing tail lemma, whose result expression is `Call ret_type (ExtCall stat fsig) es drv`. Source was reverted and focused build restored. (`TO_type_system_rewrite-20260531T201607Z_m0048_t001`, `TO_type_system_rewrite-20260531T201607Z_m0050_t001`)
- `E0004` (proved, , actual effort: 1 sessions, 5 steps, 4 tools, 2 holbuild, 448,149 tok (446,738 in, 1,411 out, 439,168 cached), 142.5s, $0.299764)
  - Inserted corrected `extcall_after_state_update_tail_sound[local]` using `Call ret_type (ExtCall stat (func_name,arg_types,ret_type)) es drv`; derived updated-state `runtime_consistent` via `update_accounts_transient_runtime_consistent`, then applied `extcall_return_tail_sound` with `metis_tac[]` for the driver-IH weakening and existential tail equation premises. -> Focused `holbuild(targets=["vyperTypeStmtSoundnessTheory"], timeout=120)` succeeded; C1.1.1 boundary lemma is proved and source kept. (`TO_type_system_rewrite-20260531T201607Z_m0065_t001`)

### Evidence refs

- `TO_type_system_rewrite-20260531T201607Z_m0065_t001` (use `read_tool_output` for exact output)

## C1.1.2

### Current Status

- result: `stuck`
- diagnosis: `risk_mismatch` The plan expected a standard helper composition, but the proof needs additional factoring or a different helper interface around the post-run_ext_call tail equality/no-type-error packaging.
- latest episode: `E0006`
- blocker: Standalone helper proof requires brittle low-level evaluator-tail plumbing; current C1.1.2 decomposition/interface is not straightforward enough for the task contract.
- actual effort: 1 sessions, 4 msgs, 53 steps, 68 tools, 15 holbuild, 5,470,012 tok (5,455,465 in, 14,547 out, 5,277,056 cached), 625.3s, $3.966983
- next: Call plan_oracle review for C1.1.2 with the failure evidence; request decomposition around a smaller tail/evaluator-prefix boundary or permission to revert the partial helper.

### Attempts / Evidence

- `E0005` (progressed, other, actual effort: 1 sessions, 9 steps, 14 tools, 2 holbuild, 1,212,028 tok (1,210,034 in, 1,994 out, 1,180,032 cached), 122.9s, $0.799846)
  - Temporarily replaced the ExtCall Resume cheat with `FAIL_TAC "probe_extcall_c112"` to inspect the live generated IH shapes needed by the standalone helper, then restored the cheat and rebuilt. -> Probe confirmed the Resume has exactly two relevant IH assumptions: driver IH (including expression and place branches for `THE drv`, guarded by `returnData = [] ∧ IS_SOME drv`) and argument-list IH for `eval_exprs cx es`. The top goal is >4KiB, reinforcing that C1.1.2 should introduce a helper rather than prove inside the Resume. Source was restored and focused build is clean. (`TO_type_system_rewrite-20260531T201607Z_m0084_t001`, `TO_type_system_rewrite-20260531T201607Z_m0086_t001`)
- `E0006` (stuck, risk_mismatch, actual effort: 1 sessions, 4 msgs, 53 steps, 68 tools, 15 holbuild, 5,470,012 tok (5,455,465 in, 14,547 out, 5,277,056 cached), 625.3s, $3.966983)
  - Added standalone `extcall_expr_sound_from_generated_ih` with return-type annotation, consuming args IH and driver IH, then stepped ExtCall evaluator prefix to call `extcall_after_state_update_tail_sound`. -> The proof did not remain straightforward: after several refinements, applying the tail bridge required brittle manual case plumbing and produced matching/timeouts/FOL-solver failures in the static success branch. This violates the component's Risk-2 expectation and the task instruction to stop on unexpected design/proof issues. (`TO_type_system_rewrite-20260531T201607Z_m0112_t001`, `TO_type_system_rewrite-20260531T201607Z_m0129_t001`, `TO_type_system_rewrite-20260531T201607Z_m0149_t001`, `TO_type_system_rewrite-20260531T201607Z_m0151_t001`)

### Ruled Out

- Inline ExtCall Resume proof remains ruled out by prior >4KiB probe.
- Direct broad evaluator stepping inside the standalone helper led to repeated non-straightforward obligations and timeout/matching failures.

### Evidence refs

- `TO_type_system_rewrite-20260531T201607Z_m0151_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260531T201607Z_m0152_t002` (use `read_tool_output` for exact output)

## C1.1.2.0

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0007`
- blocker: 
- actual effort: 1 sessions, 4 steps, 3 tools, 1 holbuild, 569,970 tok (569,517 in, 453 out, 562,176 cached), 111.9s, $0.331383

### Attempts / Evidence

- `E0007` (proved, , actual effort: 1 sessions, 4 steps, 3 tools, 1 holbuild, 569,970 tok (569,517 in, 453 out, 562,176 cached), 111.9s, $0.331383)
  - Deleted the failed partial `extcall_expr_sound_from_generated_ih` block from E0006 while keeping the small `env_consistent_get_tenv` helper, then rebuilt `vyperTypeStmtSoundnessTheory`. -> Focused build succeeded, confirming no unfinished failed proof remains and the cleanup gate is complete. The only source change left for this component is the build-clean local helper `env_consistent_get_tenv`. (`TO_type_system_rewrite-20260531T201607Z_m0158_t001`, `TO_type_system_rewrite-20260531T201607Z_m0159_t001`)

### Evidence refs

- `TO_type_system_rewrite-20260531T201607Z_m0159_t001` (use `read_tool_output` for exact output)

## C1.1.2.1

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0008`
- blocker: 
- actual effort: 1 sessions, 1 msgs, 12 steps, 12 tools, 4 holbuild, 711,735 tok (708,877 in, 2,858 out, 671,232 cached), 226.2s, $0.609581
- next: Call plan_oracle review for C1.1.2.1, then if accepted commit the source checkpoint without GPG signing before beginning C1.1.2.2.

### Attempts / Evidence

- `E0008` (proved, , actual effort: 1 sessions, 1 msgs, 12 steps, 12 tools, 4 holbuild, 711,735 tok (708,877 in, 2,858 out, 671,232 cached), 226.2s, $0.609581)
  - Added local theorem extcall_success_continuation_sound after env_consistent_get_tenv; simplified assert/update suffix, rewrote get_tenv from runtime_consistent/env_consistent_get_tenv, extracted evaluate_type witness from well_formed_type, and applied extcall_after_state_update_tail_sound with explicit conjunct/witness discharge. -> Focused build of vyperTypeStmtSoundnessTheory succeeded, validating the new boundary lemma in source. (`TO_type_system_rewrite-20260531T201607Z_m0180_t001`)
  - Initial proof ended with broad metis_tac after irule extcall_after_state_update_tail_sound. -> Failed/timed out on the packaged existential/conjunct goal; replaced with explicit conjunct_tac and qexistsl, avoiding broad FOL search. (`TO_type_system_rewrite-20260531T201607Z_m0176_t001`, `TO_type_system_rewrite-20260531T201607Z_m0178_t001`)

### Evidence refs

- `TO_type_system_rewrite-20260531T201607Z_m0180_t001` (use `read_tool_output` for exact output)
