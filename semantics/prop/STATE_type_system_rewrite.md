# STATE_type_system_rewrite
Updated: 2026-05-31

## Cursor
- component: C1.1.2
- status: in_progress
- active_file: semantics/prop/vyperTypeStmtSoundnessScript.sml
- next_action: Continue active C1.1.2. Add a standalone local helper (planned name `extcall_expr_sound_from_generated_ih`) in `vyperTypeStmtSoundnessScript.sml` near the ExtCall helper block, using the probed generated IH assumptions: argument-list IH for `eval_exprs cx es` and driver IH for `eval_expr cx (THE drv)`. Keep the conclusion on `Call ret_type (ExtCall stat (func_name,arg_types,ret_type)) es drv`. Do not edit the ExtCall Resume except for later C1.1.3 integration.
- expected_goal_shape: Helper proof should start from ordinary consistency assumptions, `well_typed_expr env (Call ret_type (ExtCall stat (func_name,arg_types,ret_type)) es drv)`, the args IH, driver IH, and an eval equation for that ExtCall. After controlled `Once evaluate_def`, split on `eval_exprs`; successful path gets `exprs_runtime_typed`, destination/value facts, `run_ext_call_accounts_well_typed`, then delegates return tail to `extcall_after_state_update_tail_sound`. No arbitrary `loc`; no full Resume proof goal >4KiB.
- verify_with: holbuild(targets=["vyperTypeStmtSoundnessTheory"], timeout=120)

## If This Fails
- If the helper formulation does not line up with C1.1.1/tail lemma after 2 honest attempts, use checkpoint_progress with the exact holbuild output; if the helper interface itself appears wrong (needs arbitrary `loc`, manual huge plumbing, or broad evaluator unfolding), close_component(result='stuck', diagnosis_tag='risk_mismatch' or 'wrong_statement') and call plan_oracle review. Do not move to C1.1.3 or C1.2.1 until C1.1.2 is proved/reviewed.

## Do Not Retry
- Prove `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall]` inline by unfolding `evaluate_def` and simplifying the whole continuation.: Prior inline attempts and the fresh probe expose >4KiB continuation goals and timeouts; this violates C1.1.2/C1.1.3 split. Use a standalone helper first.
  - evidence: episode:E0002
  - evidence: tool_output:TO_type_system_rewrite-20260531T201607Z_m0084_t001
- Use a helper conclusion with `Call loc (ExtCall stat (func_name,arg_types,ret_type)) es drv` and no `loc = ret_type` assumption.: HOL generated impossible side conditions (`ret_type = loc`, `evaluate_type ... loc`) when applying the tail lemma. All ExtCall helper conclusions should use `Call ret_type ...`.
  - evidence: episode:E0003
  - evidence: tool_output:TO_type_system_rewrite-20260531T201607Z_m0048_t001
- Begin C1.2.1 / RawCallTarget before C1.1.2, C1.1.3, and C2.1 are closed.: PLAN now explicitly says C1.2.1 is late-priority and blocked on C1.1.3 and C2.1; scheduler was repaired after two oracle calls.
  - evidence: tool_output:TO_type_system_rewrite-20260531T201607Z_m0076_t001
  - evidence: tool_output:TO_type_system_rewrite-20260531T201607Z_m0077_t001
- Use broad `gvs[]`/large `simp[]` on goals containing the full ExtCall monadic continuation.: It traverses the entire continuation and caused timeouts/huge goals; use boundary lemmas and targeted rewrites/case splits in the standalone helper.
  - evidence: episode:E0002
  - evidence: tool_output:TO_type_system_rewrite-20260531T201607Z_m0030_t001
  - evidence: tool_output:TO_type_system_rewrite-20260531T201607Z_m0034_t001

## Reflection
### Tunnel Vision Check
- Outside-the-box: instead of proving a huge full `extcall_expr_sound_from_generated_ih`, consider extracting one more smaller boundary for the evaluator prefix after `run_ext_call` success, with exact assumptions `accounts_well_typed accounts'` and the tail equation, then make C1.1.2 a thin wrapper.
- Do not optimize the Resume proof; C1.1.3 owns Resume plumbing. C1.1.2 should optimize the helper interface so the Resume can apply it without quoted-assumption theorem construction.
- The PLAN decomposition is still plausible: C1.1.1 successfully isolated record update/tail soundness; C1.1.2 should isolate evaluator prefix; C1.1.3 should only select IHs.
- If tactics start requiring full case-expression quoted assumptions or long `MATCH_MP`/`ACCEPT_TAC` plumbing, the helper statement is probably wrong-shaped. Stop and refine/escalate instead of tuning tactics.
- A fresh expert would first compare `evaluate_def` ExtCall lines 1206--1240 against the helper statement and check that `well_typed_expr_def` forces `v15 = ret_type` before any evaluator stepping.

### What Went Wrong
- The old C1.1.1 statement used arbitrary `loc`; applying `extcall_return_tail_sound` generated impossible side conditions `ret_type = loc` and `evaluate_type ... loc`. This was closed as E0003 and repaired by strategist.
- The scheduler briefly selected C1.2/C1.2.1 before its own prerequisites; two strategist calls repaired metadata/priority so current Oracle next is correctly C1.1.2.
- For C1.1.2, only a probe was done: inserting `FAIL_TAC "probe_extcall_c112"` in the ExtCall Resume showed a >4KiB goal. This confirms helper extraction is required; no helper theorem has been added yet.

### Ignored Signals
- The probe goal's first assumption is a large generated driver IH guarded by `returnData = [] ∧ IS_SOME drv`; do not treat it as a normal simple IH in the helper without preserving the guard or adapting it to the tail lemma.
- The existing `extcall_after_state_update_tail_sound` expects a driver IH without the place branch and with `functions_well_typed cx` in the antecedent; use `metis_tac[]`/a small adapter to weaken the probed driver IH rather than rebuilding it by hand.
- Current git status before handoff had PLAN/DOSSIER/task-memory changes after checkpoint/oracle activity plus untracked `LEARNINGS_type_system_rewrite.legacy.md`; source had been restored after the probe.

### Strategy Adjustments
- Start next session by checking git status and query_plan; continue C1.1.2 only if still active/beginable.
- Formulate C1.1.2 with `ret_type` as the call annotation from the beginning. Use `well_typed_expr_def` only to extract `well_typed_exprs`, `well_typed_opt`, `evaluate_type`, `MAP expr_type`, and driver type facts.
- In the helper, use controlled monadic rewrites (`Once evaluate_def`, `bind_def`/`ignore_bind_def`, targeted `TOP_CASE_TAC`) and immediately apply argument IH after `eval_exprs`; avoid unqualified `gvs[]` over the whole ExtCall continuation.
- Use proved C1.1.1 lemma as the only return-tail boundary after `run_ext_call` success and account/tStorage update; do not unfold ABI decode or `extcall_return_tail_sound`.

### Oracle Feedback
- Strategist's correction for C1.1.1 held: changing the result expression to `Call ret_type ...` made the tail bridge direct and build-clean (E0004).
- Strategist's C1.2 scheduling repair initially missed harness behavior; a second replace with late priority fixed the visible frontier so C1.1.2 is now Oracle next.
- The current strategist insight remains to add `extcall_expr_sound_from_generated_ih` before touching the Resume; the live probe supports that because the Resume goal is too large for inline proof.

## Evidence Pointers
- episode:E0004 - C1.1.1 proved/reviewed; `extcall_after_state_update_tail_sound` is available in source.
- tool_output:TO_type_system_rewrite-20260531T201607Z_m0065_t001 - focused build succeeded after adding corrected C1.1.1 theorem.
- tool_output:TO_type_system_rewrite-20260531T201607Z_m0067_t001 - strategist accepted C1.1.1 proof; no PLAN changes.
- episode:E0005 - C1.1.2 non-terminal probe recorded; active component remains open.
- tool_output:TO_type_system_rewrite-20260531T201607Z_m0084_t001 - `FAIL_TAC` probe of ExtCall Resume shows generated args IH, driver IH, and >4KiB goal.
- tool_output:TO_type_system_rewrite-20260531T201607Z_m0086_t001 - focused build clean after restoring the ExtCall Resume cheat.
- tool_output:TO_type_system_rewrite-20260531T201607Z_m0077_t001 - current frontier after scheduler repair: active/Oracle next is C1.1.2.
- source:semantics/vyperInterpreterScript.sml:1206-1240 - ExtCall evaluator branch shape to mirror in helper.
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:9616-9648 - proved C1.1.1 bridge theorem.
