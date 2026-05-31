# DOSSIER: type_system_rewrite

PLAN: `semantics/prop/PLAN_type_system_rewrite.md`

## Component Index

| Component | Status | Diagnosis | Latest Episode | Next |
|---|---|---|---|---|
| C0 | proved |  | E0001 |  |
| C1.1 | stuck | risk_mismatch | E0002 | Ask strategist to replace/augment C1.1 with an explicit standalone `extcall_expr_sound` theorem statement copied from the live generated-IH context, plus a small tail bridge helper if needed. |
| C1.1.1 | proved |  | E0004 |  |

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
