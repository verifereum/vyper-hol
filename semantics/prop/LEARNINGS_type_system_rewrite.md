# LEARNINGS_type_system_rewrite

Reusable proof patterns only. Greppable structured entries; evidence refs point to episodes/tool outputs/source.

## L0002 scope='C1.1.1' tags=runtime_consistent,record-update,extcall_return_tail_sound,update_accounts_transient
shape: Need ExtCall result after `base_st with <| accounts := accounts'; tStorage := tStorage' |>`
pattern: Bridge the post-run external-call state by deriving `runtime_consistent env cx (base_st with <| accounts := accounts'; tStorage := tStorage' |>)` from `runtime_consistent env cx base_st` and `accounts_well_typed accounts'` via `update_accounts_transient_runtime_consistent`, then apply `extcall_return_tail_sound` unchanged to the supplied return-tail equation.
works_when: The return data path is already isolated as `(if returnData=[] /\ IS_SOME drv then eval_expr cx (THE drv) else do ... od) updated_st = (res,st')` and the caller has driver typing/IH premises.
evidence:
- tool_output:TO_type_system_rewrite-20260531T201607Z_m0040_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:9561-9594

## L0003 scope='C1.1' tags=ExtCall,annotation,expr_result_typed,well_typed_expr_def
shape: ExtCall soundness helper conclusion mentions `expr_result_typed env (Call ?ty (ExtCall stat (func_name,arg_types,ret_type)) es drv) tv`.
pattern: Use the external signature return type as the `Call` annotation (`Call ret_type ...`). If a helper keeps an arbitrary annotation variable, applying tail/result-typing lemmas will demand `ret_type = loc` and type evaluation at `loc`. Extract/normalize the annotation equality from `well_typed_expr_def` before invoking helpers.
works_when: Applies to ExtCall statement/expression soundness helpers whose target is `ExtCall _ (_,arg_types,ret_type)` and whose result typing is delegated to `extcall_return_tail_sound` or `extcall_after_state_update_tail_sound`.
evidence:
- episode:E0003
- episode:E0004
- tool_output:TO_type_system_rewrite-20260531T201607Z_m0048_t001
- tool_output:TO_type_system_rewrite-20260531T201607Z_m0065_t001

## L0004 scope='C1.1.2' tags=ExtCall,Resume,generated-IH,FAIL_TAC,helper-boundary
shape: Suspended ExtCall Resume has generated args IH plus guarded driver IH and a >4KiB evaluator-success implication.
pattern: Probe the Resume only to identify generated IH shapes, then restore the cheat and prove a standalone helper. The helper should consume the args IH (`eval_exprs cx es`) and a driver IH for `THE drv`; the Resume should later only select/name those IHs and apply the helper.
works_when: Use when a suspended mutual-theorem branch has a large evaluator continuation but the needed IHs are visible at the top-level Resume goal.
evidence:
- episode:E0005
- tool_output:TO_type_system_rewrite-20260531T201607Z_m0084_t001
- tool_output:TO_type_system_rewrite-20260531T201607Z_m0086_t001

## L0005 scope='C1.1.2' tags=ExtCall,boundary-lemma,tail-bridge,monadic-suffix,risk-mismatch
shape: A helper proof reaches successful ExtCall branch and then tries to apply `extcall_after_state_update_tail_sound` directly inside static/nonstatic prefix cases.
pattern: Factor the common successful suffix into its own boundary lemma before proving the generated-IH wrapper. The suffix lemma should own `assert T`, `update_accounts`, `update_transient`, `get_tenv` rewriting, `evaluate_type_well_formed`, and the call to `extcall_after_state_update_tail_sound`; the final wrapper should stop prefix reasoning at `run_ext_call` success and apply the boundary.
works_when: Use when static and nonstatic ExtCall branches share the same post-`run_ext_call` continuation and direct application of the tail bridge starts requiring repeated existential packaging or no-type-error rewrite plumbing.
evidence:
- episode:E0006
- tool_output:TO_type_system_rewrite-20260531T201607Z_m0151_t001
- tool_output:TO_type_system_rewrite-20260531T201607Z_m0154_t001

## L0006 scope='C1.1.2' tags=env_consistent,get_tenv,timeout,rewrite-helper
shape: Large goal needs `get_tenv cx = env.type_defs` from `env_consistent env cx st`.
pattern: Use the local helper `env_consistent_get_tenv` rather than unfolding `env_consistent_def`/`env_context_consistent_def` in a large monadic proof goal; direct simplification timed out in E0006, while the small helper is build-clean after C1.1.2.0.
works_when: Applies in ExtCall suffix/prefix helpers where the environment consistency premise is available and `evaluate_abi_decode_return (get_tenv cx) ...` must be rewritten to `env.type_defs`.
evidence:
- episode:E0007
- tool_output:TO_type_system_rewrite-20260531T201607Z_m0136_t001
- tool_output:TO_type_system_rewrite-20260531T201607Z_m0159_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:9650-9654

## L0007 scope='C1.1.3' tags=ExtCall,Resume,annotation,well_typed_expr_def,helper-unification
shape: Resume goal has `expr_result_typed env (Call v15 (ExtCall ... ret_type) es drv)` but helper conclusion is for `Call ret_type (ExtCall ... ret_type) es drv`.
pattern: Before `irule extcall_expr_sound_from_generated_ih` in the ExtCall Resume, expose the call-annotation equality from `well_typed_expr_def` (`v15 = ret_type`) and simplify/substitute it; otherwise `irule` reports No match even though the helper is proved.
works_when: Applies in C1.1.3 after selecting `actual_ih` and `driver_ih`, with a live assumption `well_typed_expr env (Call v15 (ExtCall is_static' (func_name,arg_types,ret_type)) es drv)`. Keep this as local Resume plumbing; do not unfold `evaluate_def`.
evidence:
- tool_output:TO_type_system_rewrite-20260531T201607Z_m0242_t001
- episode:E0010
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:17058-17060

## L0008 scope='C1.1.3' tags=ExtCall,generated-IH,guarded-IH,simp-timeout,proof-interface
shape: Resume has generated `driver_ih` guarded by a long ExtCall success prefix, while a helper wants a pure `!env st res st'. ... eval_expr cx (THE drv) ...` premise.
pattern: Do not try to coerce the guarded generated IH into a pure premise by broad `simp` in the Resume, and do not simply add the huge guarded IH as a premise to an existing helper that relies on broad `simp`/`gvs`. The boundary must either use the guarded IH only at the exact prefix point with targeted assumption handling, or be a new helper designed to avoid putting the guarded theorem in global simplification context.
works_when: Applies to ExtCall-style suspended mutual proofs where a recursive call occurs only under a monadic success prefix and generated IHs are guarded by that prefix.
evidence:
- episode:E0011
- episode:E0014
- tool_output:TO_type_system_rewrite-20260531T201607Z_m0256_t001
- tool_output:TO_type_system_rewrite-20260531T201607Z_m0283_t001
- tool_output:TO_type_system_rewrite-20260531T201607Z_m0303_t001

## L0009 scope='C1.1.3' tags=ExtCall,conditional-IH,boundary_lemma,generated-IH,simp-timeout
shape: Continuation helper needs driver soundness only under `returnData = [] /\ IS_SOME drv`
pattern: For ExtCall success-tail soundness, use a conditional driver-IH premise (`returnData = [] /\ IS_SOME drv ==> pure driver IH`) rather than an unconditional pure IH or a theorem carrying all generated ExtCall prefix variables. This keeps the generated guarded IH local to the Resume branch where the condition and prefix facts are live.
works_when: Applies to `eval_all_type_sound_mutual[Expr_Call_ExtCall]` and similar monadic evaluator branches where a recursive call occurs only in one tail case after success-prefix checks/updates.
evidence:
- tool_output:TO_type_system_rewrite-20260531T201607Z_m0355_t001
- episode:E0015
- episode:E0017

## L0010 scope='C1.1.3.1' tags=runtime_consistent,get_tenv,NoAsms,large-context
shape: Need `get_tenv cx = env.type_defs` in a large proof context with guarded IH assumptions present
pattern: Avoid `metis_tac` or broad `gvs` over the entire context. Move only the relevant `runtime_consistent`/`env_consistent` assumption to the goal and simplify with `NoAsms` plus the minimal definitions, or prove/use a tiny extraction lemma once.
works_when: Applies when large generated IH/conditional assumptions are in context and the desired fact is a simple projection from `runtime_consistent` or `env_consistent`.
evidence:
- tool_output:TO_type_system_rewrite-20260531T201607Z_m0365_t001
- episode:E0017

## L0011 scope='C1.1.3.2' tags=ExtCall,generated-IH,adapter,simp-timeout,proof-interface
shape: Generated `driver_ih` is guarded by the full ExtCall prefix; even branch-local adapter specialization leaves a >4KiB implication
pattern: Do not treat generated ExtCall `driver_ih` consumption as local tactic work. Broad simplification and explicit full-prefix specialization both time out, even after static-branch variables are concrete. A viable redesign must avoid carrying the generated prefix through the Resume proof text (e.g. change suspension/generation interface or prove a helper matched to the generated IH outside this context).
works_when: Applies to C1.1.3.2 and descendants when trying to derive the compact conditional driver premise required by `extcall_success_continuation_sound_cond_driver_ih` from the generated mutual induction IH.
evidence:
- episode:E0019
- episode:E0020
- tool_output:TO_type_system_rewrite-20260531T201607Z_m0433_t001
- tool_output:TO_type_system_rewrite-20260531T201607Z_m0442_t001

## L0012 scope='C1.1.3.2' tags=HOL4,large-context,drule_all,metis-timeout
shape: Simple side fact in a large Resume context: `run_ext_call ... = SOME (...,accounts',...)` and `accounts_well_typed accounts` imply `accounts_well_typed accounts'`
pattern: In large generated-IH contexts, replace broad `metis_tac[run_ext_call_accounts_well_typed]` with targeted forward chaining: `drule_all run_ext_call_accounts_well_typed >> simp[]`. This avoids searching over labelled/generated assumptions.
works_when: Only for small side facts whose theorem antecedents are already live assumptions; it does not solve the generated driver-IH prefix problem.
evidence:
- episode:E0019
- tool_output:TO_type_system_rewrite-20260531T201607Z_m0417_t001

## L0014 scope='C1.1' tags=ExtCall,generated-IH,operator-stop,proof-interface,simp-timeout
shape: Generated driver_ih is guarded by the full ExtCall prefix, but the continuation helper needs only a small conditional driver premise under returnData = [] /\ IS_SOME drv.
pattern: After both monolithic Resume refactor and branch-local adapter attempts require simplifying/specializing the full generated ExtCall prefix, stop under the task contract instead of adding another local adapter. A viable continuation must redesign the proof-generation/suspension/source-theorem boundary so the driver-continuation premise is explicit, not hidden behind generated monadic prefix plumbing.
works_when: Applies only after accepted risk-mismatch evidence shows repeated generated-IH prefix attempts time out and the task explicitly requires stopping on non-straightforward design issues; this is not an unprovability result without a checked counterexample.
evidence:
- episode:E0019
- episode:E0020
- episode:E0022
- episode:E0023
- tool_output:TO_type_system_rewrite-20260531T201607Z_m0467_t001

## L0015 scope='C1.1' tags=ExtCall,driver_ih,generated-prefix,boundary-lemma,risk_mismatch
shape: Generated mutual-induction IH has a huge ExtCall prefix; local proof needs only a small conditional driver-continuation premise.
pattern: Do not package or simplify the full generated ExtCall prefix in consumer proofs. A useful boundary is a continuation helper whose premise is already the compact conditional driver IH; if the consumer cannot obtain that premise directly, the proof interface/suspension boundary must be redesigned rather than wrapped by another adapter.
works_when: Applies when holbuild exposes >4KiB generated-prefix implications or simplification timeouts while trying to specialize driver_ih in Expr_Call_ExtCall. The continuation-side helper can remain useful, but extraction of its driver premise must be addressed at a higher abstraction boundary.
evidence:
- episode:E0018
- episode:E0019
- episode:E0020
- tool_output:TO_type_system_rewrite-20260531T201607Z_m0439_t001
- tool_output:TO_type_system_rewrite-20260531T201607Z_m0442_t001

## L0016 scope='C1.1' tags=task-contract,stop-condition,partial-diff,commit
shape: Task says proof should be straightforward and to stop on design/plan issues; source has partial failing proof edits.
pattern: After an accepted operator-stop/design blocker, do not treat mechanical PLAN frontier entries as authorization for unrelated proof work. Leave partial/failing source diffs uncommitted until an operator-approved redesign or cleanup component produces a reviewed build-clean checkpoint; use git commit --no-gpg-sign only after that.
works_when: Applies when the strategist has accepted a report-only/blocked component and downstream roots are preserved but explicitly deferred by the stop condition.
evidence:
- episode:E0022
- episode:E0023
- tool_output:TO_type_system_rewrite-20260531T201607Z_m0473_t001
- tool_output:TO_type_system_rewrite-20260531T201607Z_m0475_t003

## L0017 scope='C1.1' tags=ExtCall,mutual-induction,driver_ih,boundary-lemma,generated-prefix
shape: A continuation helper is easy when given a compact conditional IH premise, but deriving that premise from a generated mutual-induction driver_ih requires simplifying a huge monadic ExtCall prefix.
pattern: Do not package the generated prefix into another local adapter. Treat the generated-IH extraction as a proof-interface/design problem: move the suspend/source theorem boundary so the recursive driver continuation premise is explicit, or redesign the mutual proof interface. Keep small continuation-boundary lemmas only when their premises can be obtained without generated-prefix plumbing.
works_when: Applies to the Expr_Call_ExtCall Resume and similar generated mutual-induction branches where a useful post-state helper closes from a compact premise but the live IH is hidden behind a large generated prefix.
evidence:
- episode:E0018
- episode:E0019
- episode:E0020
- tool_output:TO_type_system_rewrite-20260531T201607Z_m0439_t001
- tool_output:TO_type_system_rewrite-20260531T201607Z_m0442_t001

## L0019 scope='C1' tags=runtime_consistent,get_tenv,projection,targeted-simp
shape: Subgoal `get_tenv cx = env.type_defs` from `runtime_consistent env cx st`/`env_consistent env cx st` during ExtCall continuation proof.
pattern: Use a tiny local projection lemma such as `runtime_consistent_get_tenv` rather than broad unfolding/simplification of the whole runtime consistency invariant. This kept the ExtCall continuation helper proof small enough to progress.
works_when: Use when only the typing-environment projection is needed from runtime consistency and broad `gvs[runtime_consistent_def]` pollutes or fails.
evidence:
- episode:E0018
- tool_output:TO_type_system_rewrite-20260531T201607Z_m0403_t001

## L0025 scope='C1' tags=ExtCall,mutual-induction,driver_ih,proof-interface,generated-prefix
shape: Need compact premise `returnData = [] /\ IS_SOME drv ==> !env st res st'. ... eval_expr cx (THE drv) st = ... ==> ...` but live Resume only has generated `driver_ih` guarded by the full ExtCall monadic prefix.
pattern: Do not try to recover a small recursive-call premise by simplifying/specializing a generated mutual-IH hidden behind a large monadic evaluator prefix. A tautological bridge over the compact premise is useful only as an interface check; if the live context cannot supply that premise directly, the proof architecture/suspend boundary must change or the task should stop as a design blocker.
works_when: Applies to the ExtCall optional-driver branch of `eval_all_type_sound_mutual[Expr_Call_ExtCall]` where generated induction produces a prefix-guarded driver IH. Does not apply when a genuine compact IH is already a live assumption.
evidence:
- episode:E0025
- tool_output:TO_type_system_rewrite-20260531T201607Z_m0526_t001
- tool_output:TO_type_system_rewrite-20260531T201607Z_m0528_t001

## L0026 scope='C1' tags=ExtCall,continuation-helper,runtime_consistent,ABI-decode
shape: Post-run ExtCall continuation after `run_ext_call` with `accounts'`, `tStorage'`, `returnData`, and optional `drv`.
pattern: `extcall_success_continuation_sound_cond_driver_ih` is a good boundary for the post-run tail when supplied with a compact conditional driver premise; keep `runtime_consistent_get_tenv` as a tiny projection to avoid broad unfolding for `get_tenv cx = env.type_defs`. The blocker is premise availability in the Resume, not the continuation helper itself.
works_when: Use only after argument evaluation/run_ext_call success facts are local and a compact driver-continuation premise is genuinely available; otherwise escalate rather than adapting generated `driver_ih`.
evidence:
- episode:E0018
- tool_output:TO_type_system_rewrite-20260531T201607Z_m0403_t001
- episode:E0025

## L0028 scope='C0' tags=task-contract,blocked-report,cleanup,cheat-placeholder
shape: A proof branch is confirmed blocked by design, but source contains failed-probe artifacts (`FAIL_TAC` marker, tautological helper) rather than a stable placeholder/report state.
pattern: For a task that explicitly says to stop on design issues, the correct terminal action can be a cleanup/report gate: remove stale failed-probe artifacts, restore an honest placeholder if needed for build coherence, update the task plan with evidence/do-not-retry/redesign requirements, run only a minimal syntax/build check, and commit with the required no-GPG option.
works_when: Applies only after strategist review accepts the blocker and authorizes stop/report cleanup; not a substitute for proving obligations when the plan still has executable low-risk proof leaves.
evidence:
- episode:E0026
- episode:E0027
- episode:E0028
- tool_output:TO_type_system_rewrite-20260531T201607Z_m0543_t001
- tool_output:TO_type_system_rewrite-20260531T201607Z_m0559_t001

## L0029 scope='C0' tags=ExtCall,generated-IH,proof-interface,OracleBudgetExceeded,planning-gate
shape: A high-risk proof-interface blocker has no low-risk frontier; repeated required strategist calls begin returning OracleBudgetExceeded.
pattern: When the PLAN gate forbids edits/builds and the required strategist call fails with OracleBudgetExceeded, stop as an operational planning blocker rather than attempting source probes. Preserve the latest successful strategist verdict and resume only after oracle budget reset or external design input.
works_when: Applies when query_plan shows a high-risk required component with no scheduled frontier and no beginable component, and plan_oracle is the only legal next action but repeatedly fails due to budget/tool limits.
evidence:
- tool_output:TO_type_system_rewrite-20260531T201607Z_m0637_t001
- tool_output:TO_type_system_rewrite-20260531T201607Z_m0698_t001
- tool_output:TO_type_system_rewrite-20260531T201607Z_m0700_t004

## L0030 scope='C0' tags=ExtCall,proof-interface,generated-IH,planning-gate,no-build
shape: A high-risk PLAN gate forbids holbuild/source probes, but a generic operator/startup instruction says to run holbuild before continuing.
pattern: When the structured PLAN has a required high-risk gate with no frontier and explicitly forbids holbuild-as-proof-work, do not run holbuild merely to satisfy a generic startup habit. Execute the gate's legal next action (usually query_plan/plan_oracle or blocked report) and cite the conflict; build only after a replacement PLAN authorizes executable work.
works_when: Applies when query_plan shows no beginable component/no Oracle next under a blocker that explicitly covers build/probe work, and the build would be proof exploration rather than a previously authorized cleanup syntax check.
evidence:
- tool_output:TO_type_system_rewrite-20260531T201607Z_m0780_t004
- tool_output:TO_type_system_rewrite-20260531T201607Z_m0778_t001

## L0031 scope='C0' tags=ExtCall,generated-IH,proof-interface,suspend,monadic-prefix,risk-mismatch
shape: A mutual `Resume` exposes a recursive-call IH only as `full_generated_prefix ==> compact_postcondition`, while a downstream continuation lemma needs just the compact driver premise.
pattern: Treat this as a proof-interface/suspend-boundary failure, not a tactic problem. Do not recover the premise by broad simplification, long specialization over generated temporaries, or an adapter that packages the same prefix. A valid redesign must expose the recursive call in compact form before the monadic prefix is accumulated; if a bounded local boundary probe still shows the generated prefix, close/escalate or stop under a straightforward-proof task contract.
works_when: Applies when the failed goal contains large generated evaluator-prefix assumptions (`eval_exprs`, checks/lifts, calldata/run/update operations) guarding the recursive IH, and attempts to split locally require broad simp/gvs or theorem plumbing rather than small branch proofs.
evidence:
- episode:E0029
- tool_output:TO_type_system_rewrite-20260531T201607Z_m0862_t001
- tool_output:TO_type_system_rewrite-20260531T201607Z_m0881_t001
- tool_output:TO_type_system_rewrite-20260531T201607Z_m0885_t001
- tool_output:TO_type_system_rewrite-20260531T201607Z_m0886_t001

## L0034 scope='C0.1.1.2' tags=ExtCall,Resume,generated-IH,simp-timeout,impl_tac
shape: A generated IH has been specialized and the goal is `(premises ==> post) ==> rest` inside a huge Resume context; plain `simp[]` times out.
pattern: Avoid simplifying the whole implication in context. Use `(impl_tac >- simp[]) >> strip_tac` to discharge the small premise locally and add the postcondition, while keeping the large generated prefix out of the simplifier. For call typing in the same large context, use `simp[NoAsms, Once well_typed_expr_def]` rather than assumption-enabled simp.
works_when: Applies when the premise is exactly the standard local hypotheses already present (well_typed_exprs/env/state/context/accounts/functions/evaluation equation) and broad simp is timing out because of unrelated generated-prefix assumptions.
evidence:
- episode:E0035
- tool_output:TO_type_system_rewrite-20260601T081233Z_m0995_t001
- tool_output:TO_type_system_rewrite-20260601T081233Z_m0998_t001
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1001_t001

## L0039 scope='C0.1.1.2.1' tags=ExtCall,Definition,eliminator,mk_asm,impl_tac
shape: Eliminator for a large opaque predicate fails under broad `rw[def]` or if the success-condition antecedent is not in context.
pattern: For large generated-prefix predicates, unfold with targeted `rewrite_tac[def]`, specialize the theorem, label it with `mk_asm`, strip the small success condition (`returnData=[]`, `IS_SOME drv`) before applying the labelled implication, then specialize only the compact postcondition variables.
works_when: The component's job is only to open an opaque boundary, not to prove evaluator facts; all prefix facts are already assumptions and can discharge the predicate antecedent by direct matching after the success condition is available.
evidence:
- episode:E0043
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1137_t001
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1147_t001
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1153_t001

## L0045 scope='C0.1.1.2.3' tags=Resume,ExtCall,postcondition,strip_tac,helper-interface
shape: In a mutual `Resume`, generated IH assumptions are followed directly by a conjunctive result postcondition; `strip_tac` turns the target into individual conjunct goals before a helper can match the whole postcondition.
pattern: Preserve the whole postcondition until helper application. If a helper does not match without destructing the postcondition, request a helper whose conclusion exactly matches the current goal shape rather than unfolding evaluator definitions at the Resume entry.
works_when: Applies to generated mutual proof Resume blocks where the target is a multi-conjunct soundness postcondition and helper conclusions prove the entire postcondition at once.
evidence:
- episode:E0051
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1302_t001
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1304_t001

## L0046 scope='C0.1.1.2.3.1' tags=ExtCall,generated-IH,proof-interface,drule_all,irule,witness-plumbing
shape: A generated-prefix predicate/eliminator is available for ExtCall and all live prefix assumptions are present, but both manual consumer proof and standalone live-matching probe fail unless prefix witnesses are supplied explicitly.
pattern: Treat the eliminator as a failed consumer boundary, not as a theorem to instantiate harder. A valid replacement must change the theorem/suspend boundary so the compact conditional driver IH is exposed directly or prove a genuinely matchable small boundary whose probe succeeds. Do not encode generated prefix witness order in consumers, and do not trust a proved eliminator until `drule_all`/`irule` is demonstrated on the intended live-premise shape.
works_when: Applies when the goal has `returnData=[]`, `IS_SOME drv`, ExtCall success/update facts, and a needed driver expression IH, but `extcall_generated_driver_ih_elim_expr` still quantifies over `s_args`, `vs`, `args_st`, checks/lifts/run/update witnesses.
evidence:
- episode:E0055
- episode:E0056
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1350_t001
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1366_t001
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1368_t001

## L0047 scope='C0.1.1.2.3' tags=PLAN,stale-frontier,dependencies,stop-report
shape: A stop/report component is accepted for a proof-interface blocker, but sibling/dependent proof components remain scheduled and reference helpers invalidated by the stop/report.
pattern: Before doing proof work after a stop/report replacement, grep for named helper prerequisites and inspect query_plan dependencies. If a scheduled proof leaf depends on an absent or invalidated helper, close it as `plan_incomplete` and request ancestor/whole-plan repair; do not resurrect the helper locally.
works_when: Applies after a strategist converts a subtree to stop/report or invalidates prior proof frontiers but the PLAN still contains sibling/audit components with dependencies on the old proof path.
evidence:
- episode:E0057
- episode:E0058
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1380_t001
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1382_t002
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1385_t001

## L0048 scope='C0.1.1.2.4' tags=PLAN-gate,OracleBudgetExceeded,stop-state,commit-hygiene
shape: A final audit component is closed and source/build status is clean, but mandatory strategist review fails with OracleBudgetExceeded and query_plan has no frontier.
pattern: Treat this as an operational planner gate, not a proof obligation. Do not commit the regenerated DOSSIER or start sibling proof work until the review succeeds or an explicit blocked outcome is accepted. On resume, retry the exact review with compact evidence; if it fails again, report a tooling/planner blocker with the audit and oracle-failure IDs.
works_when: Applies when close_component has recorded a terminal audit episode, query_plan says the only allowed next action is plan_oracle(mode='review') for that episode, and repeated plan_oracle calls return OracleBudgetExceeded/schema errors.
evidence:
- episode:E0063
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1428_t001
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1429_t001
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1430_t001
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1431_t001

## L0049 scope='C0.1.1.2' tags=ExtCall,stop-state,audit,cheat,source-hygiene
shape: A proof branch is intentionally stopped with an original `Resume ...: cheat QED`, and final work is to audit absence of invalidated helper artifacts rather than prove the cheat.
pattern: For stop-state audit leaves, use narrow status/diff/grep/holbuild checks: confirm the intended cheat placeholder remains, invalidated helper names are absent, and the target builds. Record this as blocker/report evidence, not as theorem completion. Keep scratch/legacy untracked files unstaged.
works_when: Applies under an accepted stop/report plan where the task says to stop if proof is not straightforward and the source is expected to remain build-clean with an explicit cheat placeholder.
evidence:
- episode:E0057
- episode:E0063
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1378_t002
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1427_t001
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1427_t002
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1427_t004

## L0051 scope='C0' tags=ExtCall,operator-blocked,PLAN-frontier,stop-state,cheat,source-boundary
shape: A required proof branch is accepted as an operator-facing stop-state with an intentional `Resume ...: cheat QED`, and later proof frontiers/descendants appear or remain scheduled despite the source exposing only the blocked whole-Resume boundary.
pattern: Treat low-risk scheduled leaves after an accepted stop-state as suspect until source-boundary fidelity is checked. If a probe shows the planned focused subgoal does not exist and the task contract says to stop on non-straightforward design issues, escalate/replace the ancestor PLAN to a blocked operator-facing state rather than proving siblings or inventing local subgoals. Build-clean evidence with a cheat is blocker/report evidence, not theorem completion.
works_when: Applies when the unresolved branch is required-for-completion, source remains build-clean only because an intentional cheat placeholder remains, and attempts to prove from the current boundary would require forbidden generated-prefix reconstruction or broad prefix cleanup.
evidence:
- episode:E0063
- episode:E0064
- episode:E0065
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1460_t001
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1467_t001
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1471_t001

## L0055 scope='C0' tags=ExtCall,Resume,generated-prefix,proof-boundary,IH,timeout
shape: A mutual Resume/monadic evaluator branch keeps an optional-recursive-call IH as `full_generated_prefix ==> post`; after local eval/argument splits, even irrelevant error branches still simplify under a >4KiB generated prefix.
pattern: Treat this as a proof-boundary/interface failure, not a tactic problem. Do not recover the compact recursive-call premise by broad simplification, generated-prefix witness plumbing, or long adapter theorems. A viable replacement must move/suspend/factor the proof before the full monadic prefix is reified, and its first live probe should close an early error branch (e.g. `eval_exprs` argument-error) without the generated driver prefix in the simplification goal.
works_when: Applies to ExtCall-like evaluator branches where recursive optional-driver IHs are generated as prefix-conditional implications and the task requires straightforward branch-local proofs; especially when `simp[no_type_error_result_def]`/`gvs` times out despite explicit IH discharge.
evidence:
- episode:E0067
- episode:E0070
- episode:E0072
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1508_t001
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1595_t001
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1599_t001
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1601_t001
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1655_t001
