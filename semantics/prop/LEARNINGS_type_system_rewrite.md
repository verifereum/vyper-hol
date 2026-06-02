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

## L0056 scope='C0.3' tags=ExtCall,Resume,generated-prefix,IH,drule_all,boundary-lemma
shape: A mutual Resume branch has a generated-prefix assumption in context, an IH of the form `!env st res st'. premises ==> post`, and live assumptions already satisfy all premises.
pattern: Prefer `qpat_x_assum ... (drule_all_then assume_tac)` to consume the IH from live assumptions. Avoid `qspecl_then ... mp_tac >> simp[]` or `impl_tac >- simp[]`, because those create an implication goal whose simplification traverses the generated prefix.
works_when: Applies when the needed IH premises are already present as assumptions and the context contains a large generated optional-driver/prefix implication that makes ordinary simplification time out.
evidence:
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1734_t001
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1736_t001
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1738_t001
- episode:E0078

## L0057 scope='C0.3' tags=ExtCall,boundary-lemma,rewrite,generated-prefix,simp-timeout
shape: A small boundary lemma rewrites a subterm/result in a huge generated-prefix branch, but `simp[lemma]`/`gvs[lemma]` times out.
pattern: Do not use the simplifier as the consumer interface. Specialize the boundary lemma with `qspec`/`drule`/`MATCH_MP`-style tactics and rewrite only the preserved equality/result, or extract a helper whose conclusion is the exact branch postcondition.
works_when: Applies when the boundary lemma itself proved cleanly outside the Resume context, but the consumer branch still contains the generated optional-driver prefix.
evidence:
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1720_t001
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1740_t001
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1744_t001
- episode:E0078

## L0058 scope='C0.3' tags=ExtCall,Resume,generated-prefix,projection-lemma,conjunct-splitting
shape: A full postcondition helper is valid outside a mutual Resume, but the live Resume subgoal is already split to one conjunct while a large generated optional-driver prefix remains in assumptions.
pattern: Do not apply the full helper directly or bridge it with simp/impl_tac in the raw context. Prove conjunct-specific projection lemmas outside the Resume context whose conclusions exactly match the split subgoals (`state_well_typed st'`, `env_consistent ... st'`, `accounts_well_typed st'.accounts`, `no_type_error_result res`, result-typed case). Then consume those projections with irule/assumption matching.
works_when: Use when a computation-boundary or full-postcondition lemma proved cleanly, but raw Resume consumer goals are split conjuncts and any implication/simp bridge traverses a generated prefix.
evidence:
- episode:E0081
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1805_t001
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1818_t001
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1824_t001

## L0059 scope='C0.3' tags=ExtCall,Resume,projection-lemma,Call-annotation,helper-interface,risk-mismatch
shape: A projection/helper for an evaluator branch mentions a `Call` node whose outer annotation was assumed equal to an inner return type, but the mutual Resume goal exposes the outer annotation as an independent variable.
pattern: Before proving consumer-shaped helpers for suspended mutual goals, inspect the live Resume goal for all constructor fields that must match, not only the semantically relevant payload fields. For ExtCall argument-error, generalize helpers over the outer `Call` annotation (`call_ty`) when evaluation ignores it in the early error branch; otherwise `irule` will fail even though the mathematical branch is correct.
works_when: Applies to evaluator boundary/projection helpers consumed by `irule` in raw Resume contexts, especially constructors like `Call loc/payload/es/extra` where some fields are syntactic annotations not used by the early evaluator branch.
evidence:
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1867_t001
- episode:E0084
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:9858

## L0060 scope='C0' tags=PLAN-frontier,scheduler,dependency,ExtCall,blocked
shape: Structured PLAN text introduces a prerequisite repair component, but query_plan schedules a downstream component as Oracle next and rejects the prerequisite begin_component call.
pattern: Treat this as a scheduler/frontier blocker, not permission to work downstream. Under a stop-on-plan-issue task, do not begin the downstream component merely because it is beginable; preserve evidence that the dependency text and frontier disagree, and resume only after scheduler/frontier repair or explicit operator authorization.
works_when: Applies when the returned PLAN and query_plan component text show a dependency/order requirement (e.g. helper repair before consumer/success branch), but Beginable now/Oracle next points to a downstream leaf and plan_oracle repair is disallowed by the gate.
evidence:
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1879_t001
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1880_t001
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1880_t002
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1881_t001

## L0061 scope='C0.3.4' tags=ExtCall,boundary-lemma,Call-annotation,projection-helper,Resume
shape: An evaluator early-error branch ignores a constructor annotation field, while downstream raw Resume goals require syntactic matching on that field.
pattern: Prove a computation lemma quantified over the ignored annotation field (e.g. `call_ty`) and derive conjunct-specific projections outside the Resume. The proof can copy the narrow computation lemma: one `Once evaluate_def` unfold plus monad primitives; projection helpers then `drule` the generalized computation lemma and `gvs[]` after instantiating all constructor fields. This avoids raw generated-prefix simplification and lets later `irule` instantiate the live annotation variable directly.
works_when: The branch returns before operations that inspect the annotation, and the downstream goal only needs state/result projections after a whole-call evaluator equation. For ExtCall argument errors, `eval_exprs ... = (INR y,args_st)` returns immediately, so `call_ty` is irrelevant to evaluation but relevant for syntactic helper matching.
evidence:
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1907_t001
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1908_t001
- episode:E0089
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:9930

## L0063 scope='C0.3.3' tags=ExtCall,Resume,generated-prefix,boundary-lemma,helper-interface
shape: A true outside-Resume postcondition helper is applied by `irule` inside a mutual Resume branch, but its premises become side-condition subgoals under a huge generated optional-driver prefix.
pattern: If helper premises cannot be discharged by direct, robust tactics in the live Resume context, the helper is still not consumer-shaped enough. Escalate for a boundary/factoring whose conclusion matches the full live goal or whose elimination rule consumes live assumptions before entering the generated-prefix subgoal; do not compensate with assumption-position or quoted-ASSUME plumbing.
works_when: Use this when the branch's mathematics is already packaged outside the Resume, but applying it still leaves side conditions in a hostile generated-prefix context. The evidence is especially strong when visible assumptions identical to side goals fail to close reliably and simplification times out.
evidence:
- episode:E0093
- tool_output:TO_type_system_rewrite-20260601T081233Z_m2024_t001
- tool_output:TO_type_system_rewrite-20260601T081233Z_m2085_t001

## L0064 scope='C0.3.3' tags=ExtCall,Resume,generated-prefix,equality-lemma,boundary-lemma,targeted-rewrite
shape: An early-error evaluator branch in a mutual Resume has the returned result/state hidden behind a large generated optional-driver prefix, and postcondition helpers/projections leave brittle side conditions.
pattern: Prefer an evaluator-only equality/elimination lemma (`res = error_result` and `st' = returned_state`) over a full postcondition helper. In the live Resume branch, derive the equality with `drule_all`, rewrite only those equality facts, then split the postcondition and close conjuncts from IH facts. This avoids generating preservation/typing premises under the generated prefix.
works_when: The branch returns before later monadic operations/driver code, and the expression-list IH already provides facts about the returned state/result. For ExtCall argument errors, `eval_exprs = INR` returns immediately for any outer `Call` annotation.
evidence:
- episode:E0096
- episode:E0097
- tool_output:TO_type_system_rewrite-20260601T081233Z_m2105_t001
- tool_output:TO_type_system_rewrite-20260601T081233Z_m2148_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:9930-9955
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:17458-17483

## L0065 scope='C0.3.3' tags=no_type_error_result,INR,generated-prefix,targeted-rewrite,sumTheory.INR_11
shape: Goal and assumption are both `no_type_error_result (INR y)` inside a large generated-prefix Resume context, but direct assumption selection, `simp[]`, `gvs[]`, or `metis_tac[]` fails/times out.
pattern: Move the exact assumption to the goal, use `pure_rewrite_tac[no_type_error_result_def]`, strip the small resulting implication, specialize the universally quantified assumption at `msg`, and rewrite the injected `INR` equality with `sumTheory.INR_11`. Avoid broad simplification of the surrounding context.
works_when: The no-type-error predicate is on an `INR` result and the surrounding assumptions include a huge generated evaluator-prefix implication that makes ordinary simplification/first-order search inspect too much context.
evidence:
- episode:E0097
- tool_output:TO_type_system_rewrite-20260601T081233Z_m2126_t001
- tool_output:TO_type_system_rewrite-20260601T081233Z_m2135_t001
- tool_output:TO_type_system_rewrite-20260601T081233Z_m2148_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:17475-17481

## L0067 scope='C0.1' tags=word_size,type_slot_size,arithmetic,FAIL_TAC-probe
shape: A theorem proof has already reduced to a single cheated arithmetic/type-slot tail after `Cases_on flags`, definition rewrites, `word_size_le`, and a `word_size n < n` split.
pattern: Use a deliberate `FAIL_TAC` probe to read the exact residual arithmetic goal before choosing between `word_size_le`, `dimword` facts, and `decide_tac`. Avoid broad rewrites or definition changes; the proof should stay local to the existing theorem statement.
works_when: The source is an infrastructure lemma like `raw_call_return_type_well_formed` where all semantic cases are already discharged and only a numeric side condition remains.
evidence:
- source:semantics/prop/vyperTypeBuiltinsScript.sml:3488-3498
- tool_output:TO_type_system_rewrite-20260601T081233Z_m2228_t001
- tool_output:TO_type_system_rewrite-20260601T081233Z_m2229_t001

## L0069 scope='C0.2.2' tags=ExtCall,Resume,generated-prefix,simp-timeout,static-branch
shape: A focused static ExtCall Resume branch has the optional-driver generated prefix as assumption 0, plus concrete `eval_exprs = INL` and argument destructor facts, and the next step is simplifying `eval_expr`/monadic prefix.
pattern: Do not ask the simplifier to reduce the whole evaluator expression in this context. Even after deriving `x <> []` and `dest_AddressV (HD x) = SOME target_addr`, `simp[...]` over the goal can traverse or retain the generated prefix and time out. First isolate the evaluator equation into a small named fact/helper or otherwise hide/remove the generated prefix from simplifier visibility; if that is not straightforward, close the component as risk_mismatch rather than retrying simplifier variants.
works_when: Applies to `eval_all_type_sound_mutual[Expr_Call_ExtCall_result_static]` and similar focused Resume branches where the generated optional-driver IH remains visible while proving ExtCall prefix cases.
evidence:
- tool_output:TO_type_system_rewrite-20260601T081233Z_m2304_t001
- tool_output:TO_type_system_rewrite-20260601T081233Z_m2310_t001
- episode:E0070

## L0071 scope='C0.2' tags=ExtCall,COND_CLAUSES,selected-rewrite,simp-timeout
shape: A tiny branch-shape assumption is of the form `if T/F then MAP expr_type es = ... else ...` while a generated-prefix universal is visible in assumptions.
pattern: If a selected conditional fact must be normalized, move only that fact and use `pure_rewrite_tac[boolTheory.COND_CLAUSES]`; do not use `simp[]`. In nonstatic, this derived `MAP expr_type es = BaseT AddressT::BaseT (UintT 256)::arg_types` plus destructor facts without touching the generated prefix; static `simp[]` timed out on the analogous step.
works_when: Use only for small selected propositions; it does not solve the later evaluator-prefix problem and should not replace the boundary-theorem refactor.
evidence:
- tool_output:TO_type_system_rewrite-20260601T081233Z_m2345_t001
- tool_output:TO_type_system_rewrite-20260601T081233Z_m2331_t001

## L0072 scope='C0.3' tags=RawCallTarget,tail-helper,boundary-lemma,run_ext_call,return-typing
shape: RawCallTarget Resume after expression-list IH reaches a huge tail goal containing `run_ext_call`, `update_accounts`, `update_transient`, flags, `raw_call_return_type`, no-TypeError, and result typing.
pattern: Do not finish this in the Resume. Factor into local helpers: (1) `raw_call_args_runtime_typed_dest` for address/bytes/uint destructors, (2) flag-dependent return value typing for `raw_call_return_type flags`, and (3) `raw_call_tail_result_sound`/`_simp` that owns the monadic tail and uses `run_ext_call_accounts_well_typed` plus update preservation. Then the Resume should mirror RawLog by invoking the tail helper.
works_when: Applies when the evaluator prefix has already split `eval_exprs` to `INL vs,args_st` and well-typed RawCallTarget facts provide length/type constraints. Keep helper statements matching the consumer nested-case/do-form shape to avoid duplicating semantic reasoning.
evidence:
- episode:E0106
- tool_output:TO_type_system_rewrite-20260601T081233Z_m2362_t001
- tool_output:TO_type_system_rewrite-20260601T081233Z_m2374_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:10289-10774

## L0073 scope='C0.2' tags=ExtCall,Resume,generated-prefix,boundary-theorem,proof-interface,premise-mismatch
shape: A mutual `Resume` ExtCall branch has an optional-driver IH available only as `full_generated_prefix ==> driver_post`, while a candidate boundary theorem (`extcall_expr_sound_from_generated_ih`) requires an unconditional driver IH premise.
pattern: Before rebasing a hostile Resume branch to a boundary theorem, compare each theorem premise against the actual generated IH shape. If the theorem wants an unconditional recursive-call IH but the context has only a prefix-guarded implication, do not retry direct theorem application or build a long adapter; request a repaired helper/interface whose premise matches the generated-prefix IH, or restructure to specialize the IH only inside the concrete success continuation.
works_when: Applies to ExtCall_result in `vyperTypeStmtSoundnessScript.sml` and similar monadic mutual-proof branches where optional recursive calls are guarded by generated evaluator-prefix facts. Equality/type normalization (e.g. `v15 = ret_type`) may be locally fixable but does not address the IH-shape mismatch.
evidence:
- episode:E0107
- tool_output:TO_type_system_rewrite-20260601T081233Z_m2388_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:10059
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:17467

## L0074 scope='C0.2' tags=oracle,planning-gate,tooling-blocker,output-validation
shape: A required `plan_oracle(mode='review')` after a closed stuck episode repeatedly fails with output-validation errors, while query_plan reports no beginable frontier.
pattern: Treat this as an operational planning/tooling blocker. Do not perform proof edits/builds or unofficial local redesigns while the PLAN gate says pending strategist review. Preserve the exact failed oracle outputs and resume by retrying/recovering the required review once tooling is fixed.
works_when: Applies when a blocking episode is recorded, query_plan lists only `plan_oracle(mode='review', ...)` as allowed next action, and repeated oracle calls fail due `UnexpectedModelBehavior` or similar tool validation rather than mathematical content.
evidence:
- tool_output:TO_type_system_rewrite-20260601T081233Z_m2392_t001
- tool_output:TO_type_system_rewrite-20260601T081233Z_m2394_t001
- tool_output:TO_type_system_rewrite-20260601T081233Z_m2396_t004

## L0079 scope='C0.2.1.1.2' tags=ExtCall,generated-IH,quarantine,Resume,success-tail,proof-interface
shape: A `Resume` ExtCall_result branch has a huge generated optional-driver IH; prefix/error branches work only if it is quarantined, but the success tail still needs a proof boundary.
pattern: Use `pop_last_assum (fn driver_ih => ...)` to remove the generated IH before static prefix simplification; broad `qpat_x_assum` and `first_x_assum` are wrong in this goal. Treat this only as a prefix-quarantine technique, not a complete proof interface. If the success tail requires direct `irule`/`match_mp_tac`, local `drule_all` generated-prefix specialization, or applying `extcall_success_continuation_sound_cond_driver_ih` after goal splitting, stop and redesign: E0114/E0116 show those routes do not align straightforwardly.
works_when: Works to reach/build the static prefix/error skeleton with a tail cheat when the generated IH is the oldest assumption. Does not solve the success tail; use it only under an authorized replacement plan that provides a new success-tail boundary and avoids generated-prefix adapters.
evidence:
- episode:E0113
- episode:E0114
- episode:E0116
- tool_output:TO_type_system_rewrite-20260601T081233Z_m2520_t001
- tool_output:TO_type_system_rewrite-20260601T081233Z_m2574_t001
- tool_output:TO_type_system_rewrite-20260601T081233Z_m2594_t001

## L0080 scope='C0.2.1' tags=ExtCall,generated-IH,quarantine,Resume,simp-timeout
shape: Resume branch contains a raw generated mutual-IH/full-prefix implication plus local ExtCall prefix/error proof obligations
pattern: If a generated full-prefix IH is live in assumptions, assumption-using simplification/case cleanup can traverse it and time out or expose unreadable goals. In this Resume shape, capturing/removing it first with `pop_last_assum (fn driver_ih => ...)` quarantines the prefix enough for error branches to build; do not leave it live during prefix simplification.
works_when: Useful only for prefix/error branch cleanup where the IH is not needed until the success tail. It does not solve the later need to consume the IH; a separate compact continuation boundary is required.
evidence:
- episode:E0111
- episode:E0113
- tool_output:TO_type_system_rewrite-20260601T081233Z_m2496_t001
- tool_output:TO_type_system_rewrite-20260601T081233Z_m2520_t001
- tool_output:TO_type_system_rewrite-20260601T081233Z_m2527_t001

## L0081 scope='C0.2.1' tags=proof-interface,driver_ih,ExtCall,boundary-lemma
shape: Helper with compact driver premise is applied after the ExtCall success-tail goal has already been split into conjunctive invariant obligations
pattern: Validate a success-tail boundary against the unsplit continuation goal before investing in branch proof text. A helper can be compact in statement yet fail after `strip_tac`/conjunct splitting; if it does not match even with its hardest premise cheated, the boundary is wrong rather than the premise proof being merely missing.
works_when: Applies to helpers intended to consume generated mutual-IH continuations or prove multiple invariant conjuncts after monadic success paths. First probe helper alignment on a minimal suspended/unsplit goal.
evidence:
- episode:E0116
- tool_output:TO_type_system_rewrite-20260601T081233Z_m2594_t001
- tool_output:TO_type_system_rewrite-20260601T081233Z_m2611_t001

## L0083 scope='C0.2.1' tags=ExtCall,generated-IH,boundary,conditional-premise
shape: Generated optional-driver IH appears as `full ExtCall prefix /\ returnData = [] /\ IS_SOME drv ==> !env st res st'. ...`, while helper wants driver soundness.
pattern: A helper requiring an unconditional driver IH is the wrong boundary for this Resume. The usable boundary must keep the driver obligation conditional on `returnData = [] /\ IS_SOME drv` and be applied only in the single success branch where prefix equations are already present.
works_when: Applies to ExtCall static/nonstatic result branches after argument evaluation and `run_ext_call` success have been isolated. If the proof must reconstruct the whole prefix outside that branch, stop/escalate.
evidence:
- episode:E0118
- tool_output:TO_type_system_rewrite-20260601T081233Z_m2632_t001
- tool_output:TO_type_system_rewrite-20260601T081233Z_m2638_t001

## L0086 scope='C0.2.1.3' tags=ExtCall,Resume,generated-IH,branch-local,proof-interface
shape: A generated mutual-IH in a suspended ExtCall Resume is a full monadic-prefix implication with extra conjuncts, while a proved helper expects an unconditional compact driver IH.
pattern: Do not consume the helper at the top of the Resume. Keep the explicit linear monadic split in the Resume until the success continuation branch where the generated prefix assumptions are concrete; then use tail lemmas such as `extcall_after_state_update_tail_sound` and project/specialize the generated IH only locally. A standalone projected helper may be a proof template, not the actual consumer interface.
works_when: Use when holbuild shows `driver_ih` guarded by the full ExtCall prefix and direct helper application leaves `MATCH_MP_TAC No match`, `DISCH_THEN` failure, or metis timeout. Applies under the maintainer rule forbidding broad generated-prefix simplification/adapters.
evidence:
- episode:E0132
- episode:E0133
- tool_output:TO_type_system_rewrite-20260601T081233Z_m2812_t001
- tool_output:TO_type_system_rewrite-20260601T081233Z_m2819_t001
- tool_output:TO_type_system_rewrite-20260601T220715Z_m2825_t001

## L0087 scope='C0.2.1.4' tags=ExtCall,generated-prefix,boundary-lemma,Resume
shape: Resume proof has a full generated optional-driver prefix assumption; local `gvs`/`simp` over monadic prefix times out or exceeds 4KiB.
pattern: Move ExtCall prefix reasoning out of the Resume into a local projected-state boundary theorem with compact assumptions and a compact optional-driver IH premise. Then make the Resume a small consumer of that boundary lemma instead of simplifying evaluator internals with the generated prefix visible.
works_when: The boundary theorem can be stated from successful `eval_exprs`, runtime-typed argument facts, MAP expression-type shape, and a compact driver-IH premise; it should conclude only the needed invariant such as `state_well_typed st'`.
evidence:
- episode:E0136
- tool_output:TO_type_system_rewrite-20260601T220715Z_m2884_t001
- tool_output:TO_type_system_rewrite-20260601T220715Z_m2894_t001

## L0088 scope='C0.2.1.4' tags=ExtCall,exprs_runtime_typed,list-nonempty,helper
shape: Need `vs <> [] /\ TL vs <> []` from nonstatic ExtCall runtime-typed args and `MAP expr_type args = Address :: Uint256 :: arg_tys`.
pattern: Prove a small helper outside the Resume context: `extcall_nonstatic_args_runtime_typed_nonempty[local]`. Use it in later boundary/helper proofs instead of unfolding `exprs_runtime_typed_def` where generated Resume assumptions are present.
works_when: The proof context is a clean local lemma over `exprs_runtime_typed env args vs` and MAP shape, not a suspended Resume branch with generated prefix implications.
evidence:
- episode:E0137
- tool_output:TO_type_system_rewrite-20260601T220715Z_m2892_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml

## L0089 scope='C0.2.1.3' tags=ExtCall,Resume,case-split,success-flag,driver-IH
shape: After `PairCases_on` a `run_ext_call` result, `Cases_on x'0` splits the ExtCall success flag before `check success`.
pattern: Verify branch orientation before placing continuation proof: the failure/revert branch closes with `no_type_error_result_def`/`raise_def`, while the success branch is where `accounts_well_typed`, `runtime_consistent`, and `extcall_success_continuation_state_well_typed` belong. Misplacing the tail theorem leaves a projected `state_well_typed st'` goal or `first subgoal not solved` failure.
works_when: Use in static/nonstatic ExtCall Resume proofs after `run_ext_call ... = SOME (...)` and `PairCases_on` have exposed the success flag and return data.
evidence:
- tool_output:TO_type_system_rewrite-20260601T220715Z_m2955_t001
- tool_output:TO_type_system_rewrite-20260601T220715Z_m2959_t001
- episode:E0140

## L0090 scope='C0.2.1.3.3' tags=ExtCall,Resume,after-update,conditional-IH,boundary-helper
shape: A Resume branch has already simplified `assert T`, `update_accounts`, and `update_transient`, so helpers over the larger `do assert; update; update; tail od` do not match the live post-update tail.
pattern: Factor an after-state-update boundary helper whose semantic equation starts at `(base_st with <| accounts := accounts'; tStorage := tStorage' |>)` and takes a conditional optional-driver IH. Prove the full ExtCall postcondition in the helper, then in the Resume derive/provide the conditional premise locally from the generated IH rather than matching a larger do-block.
works_when: Use after `run_ext_call` has returned a concrete success tuple and the Resume proof has simplified account/transient updates. Works best when ordinary state/account facts are discharged manually and the conditional driver premise is asserted explicitly.
evidence:
- episode:E0142
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3004_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml

## L0091 scope='C0.2.1.3.3.4' tags=ExtCall,Resume,projection,tail-helper,state_well_typed
shape: Suspended Resume subgoal is a projection such as `state_well_typed st'`, while available ExtCall tail helper proves a full conjunctive postcondition.
pattern: Do not `irule` a full-postcondition tail theorem directly against the projected goal. First prove/assert the full postcondition as a local fact and project, or use a state-only projection lemma whose conclusion matches the Resume subgoal. Only after this match issue is solved should the proof enter the concrete driver-IH branch.
works_when: Use in `eval_all_type_sound_mutual[Expr_Call_ExtCall_result_static]` after the linear ExtCall prefix split and success branch when holbuild reports `MATCH_MP_TAC No match` on a projected invariant goal.
evidence:
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3080_t001
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3081_t001
- episode:E0148

## L0092 scope='C0.2.1.3.3' tags=PLAN,blocked_report,status-mismatch,cheat,ExtCall
shape: A documentation leaf says to record proof completion/unblock, but source and reviewed episodes show an intentional `cheat` stop-state.
pattern: Before editing documentation-only leaves after a PLAN replacement, audit the source obligation and latest reviewed episodes. If the leaf would claim a proof is complete while source still contains an intentional `cheat`, close/escalate the leaf as wrong_statement instead of writing false status.
works_when: Use for stop-state subtrees where proof attempts were reverted and PLAN/doc leaves may be stale after replacement.
evidence:
- episode:E0151
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3106_t001
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3108_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:17638

## L0097 scope='C0.2.1' tags=ExtCall,Resume,suspend,generated-IH,proof-boundary
shape: A suspended mutual-proof subgoal still resumes to projection goals containing a full generated ExtCall prefix, rather than a small tail-helper obligation.
pattern: Treat this as evidence that the suspension boundary is still too early. Do not proceed by replaying or simplifying the generated prefix inside the Resume; ask for a helper/boundary whose conclusion matches the resumed projection obligations, or move the cut point so the helper sees only concrete post-update tail facts.
works_when: Applies when `RESUME_TAC` on a branch-local `suspend` yields >4KiB goals with the generated optional-driver IH as a guarded monadic prefix implication, and existing tail helpers do not directly match the first projection goal.
evidence:
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3225_t001
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3227_t001
- episode:E0157
- episode:E0158

## L0098 scope='C0.2.2' tags=ExtCall,Resume,generated-IH,simp-timeout,rewrite_tac
shape: A helper proof times out at `simp[Once well_typed_expr_def]` after adding nearby ExtCall boundary lemmas, before reaching the target Resume.
pattern: Use `rewrite_tac[Once well_typed_expr_def]` for the exact one-step well-typed expression unfold instead of invoking the full simplifier over a large ExtCall/IH context. This preserves the intended proof state and avoids unrelated simplifier search.
works_when: The needed step is only unfolding `well_typed_expr_def` once for a known constructor and no assumption-driven simplification is required.
evidence:
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3333_t001
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3336_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml

## L0102 scope='C0.2.3.2.1' tags=ExtCall,linear-prefix,skeleton,checkpoint
shape: Static ExtCall success Resume with intentional marker at post-update tail.
pattern: A linear prefix skeleton can reach a single concrete static ExtCall success tail while preserving useful facts (`eval_exprs`, argument runtime typing, calldata build, code check, `run_ext_call = SOME (T,q',q'',r)`, continuation equation) and labelled `generated_driver_ih`. This is a good inspection/checkpoint boundary, but not a proof of the driver premise.
works_when: Use as a baseline for further strategist-approved redesign; keep marker or restore cheat until the tail proof is solved.
evidence:
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3482_t002
- episode:E0173

## L0104 scope='C0.2.3.2.2.1' tags=ExtCall,continuation,branch-split,vacuous-IH
shape: Static ExtCall success tail with `(if returnData = [] /\ IS_SOME drv then eval_expr ... else ABI-decode) updated_st = (res,st')`; prove branches where condition is false.
pattern: Split on `returnData = [] /\ IS_SOME drv` after the monadic prefix is already linearized. In the false branch, use `extcall_after_state_update_tail_sound_cond_driver_ih` with a vacuous conditional-driver premise, plus local `runtime_consistent`, `run_ext_call_accounts_well_typed`, and direct `drule runtime_consistent_get_tenv >> simp[]`; do not mention generated_driver_ih.
works_when: The context already has concrete `run_ext_call ... = SOME (T,returnData,accounts',tStorage')`, updated-state tail equation, `state_well_typed args_st`, `env_consistent env cx args_st`, and `accounts_well_typed args_st.accounts`.
evidence:
- episode:E0175
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3510_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:17793-17811

## L0109 scope='C0.2.3.2' tags=ExtCall,Resume,suspend,generated_driver_ih,proof_boundary
shape: A generated mutual `Resume` branch is suspended at a concrete recursive-call continuation; native branch facts appear, but the recursive IH remains `full_generated_prefix ==> driver_post`.
pattern: A focused `suspend`/`Resume` boundary is useful for exposing concrete branch facts and confirming the real tail state, but it does not by itself compact a generated IH. If the Resume still exposes only `generated_driver_ih` guarded by the full monadic prefix, local `qspec` plus simplification is still generated-prefix recovery and should be treated as a proof-interface failure, not a tactic problem.
works_when: Use this pattern to distinguish useful branch-focusing from actual IH producer repair in generated mutual proofs. It applies when the focused goal has native success facts but the only recursive IH is still a full-prefix universal.
evidence:
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3610_t001
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3622_t001
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3624_t001
- episode:E0187
- episode:E0188

## L0110 scope='C0' tags=ExtCall,PLAN-gate,terminal-blocker,generated-IH,no-build,blocked
shape: Accepted terminal-blocker/bookkeeping leaf for a required theorem branch; source remains intentionally partial and query_plan may still show ready-looking descendants.
pattern: Treat the reviewed terminal disposition as blocked task evidence, not theorem progress. Do not build/probe from generic startup habits, do not start downstream leaves, and do not commit partial source. Resume proof work only after a maintainer/strategist supplies an ancestor-scoped PLAN update with a genuine low-risk proof-producer frontier that resolves the hostile generated-prefix IH (or relaxes the constraints).
works_when: Applies when strategist-reviewed evidence says a required branch exposes only a generated-prefix-shaped IH or analogous missing producer interface, the task contract says to stop on design issues, and the active leaf is `terminal_blocker_disposition`/bookkeeping rather than a HOL theorem proof.
evidence:
- episode:E0189
- episode:E0188
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3637_t001
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3640_t004
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3622_t001

## L0117 scope='C0.2.3.2.2' tags=ExtCall,branch-selection,TRY,generated_driver_ih
shape: Multi-goal Resume where driver-specific exact facts are valid only in the concrete success goal, and sibling decode/non-driver goals remain open.
pattern: Do not use `TRY (...)` to apply branch-specific proof-producing assertions across all goals; it can silently discard failures and hide absence of the intended assumption. Instead select the concrete goal first with a goal-pattern selector such as `all_tac >~ [pat] >- (...)`, replay exact facts inside that branch, and verify with a FAIL_TAC marker before deriving downstream IHs.
works_when: Applies when branch facts mention concrete success data like `run_ext_call ... = SOME (T,[],q'',r)` or updated-state driver evaluation, while sibling goals have different return-data/evaluation shapes.
evidence:
- episode:E0195
- episode:E0196
- episode:E0198
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3852_t001

## L0121 scope='C0.2.3.2.2.1' tags=suspend,Resume,Finalise,cheat,stabilization
shape: A suspended subgoal is being abandoned/stabilized with an intentional cheat, and `Finalise` reports `No resumption proof found` when the Resume body is changed to `cheat`.
pattern: For a `suspend`/`Resume` proof, an intentional-cheat baseline may need to replace the original `suspend "label"` proof point with `cheat` and remove the corresponding `Resume`, rather than putting `cheat` inside the `Resume` body. A `Resume ...: cheat` or `RESUME_TAC >> cheat` can fail `Finalise` because it does not discharge the stored resumption proof as expected.
works_when: Use only for administrative stabilization of an intentionally unfinished suspended branch, preserving theorem names and leaving a documented cheat; do not use to hide a proof obligation that the task requires to be solved.
evidence:
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3921_t001
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3923_t001
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3934_t001
- episode:E0201

## L0122 scope='C0.2.3.2.2' tags=PLAN,scheduler,dependencies,stop_gate
shape: A component is marked beginable/Oracle-next, but its own PLAN text says it is gated/not actionable pending an unresolved proof gate.
pattern: Treat this as a PLAN scheduling contradiction, not an executable proof frontier. Do not begin the component just because query_plan lists it beginable; request a broad enough PLAN replacement to preserve/gate downstream dependencies coherently, or report blocked if oracle/tooling cannot repair it.
works_when: Applies when component details explicitly contain `not_to_try`/rationale forbidding execution under the current gate and a terminal blocker/report for the prerequisite has been accepted.
evidence:
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3954_t001
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3956_t001
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3957_t001
- episode:E0203

## L0125 scope='C0.1.2' tags=ExtCall,Resume,prefix-error,SIMP_RULE,generated-prefix,timeout
shape: A branch-local prefix-error Resume has a huge generated optional-driver premise in context plus a selected evaluation equality `(case ...)= (res,st')`; goal-level `simp/gvs` times out.
pattern: Push only the selected evaluation equality with `mp_tac`, rewrite concrete branch facts into it, then consume it via `disch_then (assume_tac o SIMP_RULE (srw_ss()) [pairTheory.pair_case_thm, sumTheory.sum_case_def, bind_def, return_def, raise_def, ...])`. After the equality is simplified into concrete `res/st'` facts, use `gvs[no_type_error_result_def]` to close preservation/no-TypeError goals. Kill irrelevant generated-driver premises before final cleanup if they pollute simplification.
works_when: Works for prefix-failure branches that do not evaluate the optional driver and have concrete branch facts such as `build_ext_calldata ... = NONE` or an assertion failure. Do not use for the run-success optional-driver branch, where a real conditional driver IH is needed.
evidence:
- tool_output:TO_type_system_rewrite-20260601T220715Z_m4063_t001
- tool_output:TO_type_system_rewrite-20260601T220715Z_m4065_t001
- tool_output:TO_type_system_rewrite-20260601T220715Z_m4084_t001
- tool_output:TO_type_system_rewrite-20260601T220715Z_m4090_t001
- episode:E0207

## L0136 scope='C0.4' tags=ExtCall,generated-prefix,Resume,manual-progress,proof-boundary
shape: Static ExtCall mutual proof exposes a generated optional-driver premise before concrete `run_ext_call = SOME ...` tail facts.
pattern: If direct tail work after `Cases_on run_ext_call` yields generated-prefix fanout, do not mine the prefix. A viable boundary is to inline/structure the static branch so the administrative generated-driver premise is discharged first, then leave/prove only the concrete ExtCall tail. Keep the generated premise opaque; source reality may move the remaining cheat from a separate `*_static_success` Resume into the parent static Resume.
works_when: Applies to the static ExtCall mutual proof in `vyperTypeStmtSoundnessScript.sml` when the generated optional-driver IH is guarded by the monadic ExtCall prefix and the maintainer forbids broad prefix adapters.
evidence:
- episode:E0241
- episode:E0244
- tool_output:TO_type_system_rewrite-20260602T195240Z_m4577_t001
- tool_output:TO_type_system_rewrite-20260602T195240Z_m4577_t003

## L0137 scope='C0.5' tags=ExtCall,nonstatic,helper-boundary,generated-prefix,missing-helper
shape: Nonstatic ExtCall Resume has full mutual postcondition plus generated conditional driver IH; existing helper proves only `state_well_typed`.
pattern: Do not fill the nonstatic ExtCall Resume by copying static proof plumbing directly. First provide/decompose to a compact nonstatic full-postcondition helper or subresumes: error branches should be local/mechanical, and the success tail should invoke `extcall_after_state_update_tail_sound_cond_driver_ih` only after concrete `run_ext_call = SOME (T, returnData, accounts', tStorage')` facts are available.
works_when: Applies to C0.5 after static ExtCall is finalized and `Expr_Call_ExtCall_result_nonstatic` still contains the planned cheat; direct branch proof exposes large monadic/generated-prefix goals or timeouts.
evidence:
- episode:E0248
- tool_output:TO_type_system_rewrite-20260602T195240Z_m4638_t001
- tool_output:TO_type_system_rewrite-20260602T195240Z_m4645_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:10115

## L0138 scope='C0.5' tags=ExtCall,nonstatic,RuntimeError,branch-helper,mutual-postcondition
shape: Already-isolated nonstatic ExtCall error branch: `res = INR (Error (RuntimeError msg))` and `st' = cur_st` with current state/env/accounts invariants.
pattern: Use a tiny branch-local helper (`extcall_nonstatic_runtime_error_sound`) to close unchanged-state RuntimeError branches. The helper has no full `eval_expr (Call ... ExtCall F ...)` premise; it rewrites only `no_type_error_result_def` and returns the exact mutual postcondition, avoiding generated-prefix simplification entirely.
works_when: Applies after the final Resume has isolated calldata failure, no-code, run-none, or revert as a concrete RuntimeError with unchanged `args_st`/current state. Do not use for success branches that update accounts/transient storage.
evidence:
- episode:E0251
- tool_output:TO_type_system_rewrite-20260602T195240Z_m4682_t001
- tool_output:TO_type_system_rewrite-20260602T195240Z_m4683_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:10180
