# PLAN

## Structured Components

### C0: Carry forward baseline build/CHEAT audit and completed proof stack evidence
- Kind: `source_audit`
- Risk: 1
- Work priority: 0
- Work units: 0
- Rationale: Mechanical carry-forward. Prior evidence records that the fresh stack builds far enough to expose only the current reachable cheats; no executor proof work remains here.
- Required for completion: yes
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0, E0530, C1, E0531, E0532, E0533, E0534, E0535, E0536, C2.6 IntCall proof history, E1327, E1332, C4 ABI/default proof history, E0781

#### Summary
- Carries forward the accepted baseline and completed fresh-stack proof evidence.
- Includes completed assignment-target preservation, IntCall statement-soundness work, and prior ABI/default helper progress insofar as current source builds past them.
- No executor work is authorized in this component.
- If a later focused build regresses inside a carried theorem, stop and escalate with the exact failing theorem/location.

#### Description
This component replaces the long markdown history of already-closed assignment, IntCall, ABI, and helper subtrees with a single structured carry-forward checkpoint. It is not a license to reopen old deep proof chains. The current executable plan starts at the remaining source-authoritative reachable cheats described below.

#### Statement
Carry-forward obligation only: prior completed proof products remain accepted unless the current focused build produces a concrete regression.

#### Approach
Do not edit under C0. Use current source/build failures, not stale historical unprovability gates, to decide whether any carried theorem must be reopened.

#### Not to try
Do not broad-grep unrelated retired-theory cheats and add them as task obligations. Do not reopen the completed IntCall helper chain for style or historical cleanup.

### C1: Type-system rewrite proof obligations in statement soundness
- Kind: `proof_group`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: Risk is lowered insofar as this update only repairs the blocked ExtCall helper path under C1.1; no evidence here invalidates the top-level strategy.
- Required for completion: yes
- Progress transition: `carry_forward`
- Carries progress/evidence from: C1

#### Progress note
Parent carried forward; only C1.1.2 is repaired.

#### Summary
Carry forward the existing top-level task strategy. This update is scoped to the ExtCall helper subtree under C1.1. The previously proved C1.1.1 bridge remains valid. No sibling/cousin obligations are changed by E0006.

#### Argument
The top-level proof still proceeds by extracting local boundary lemmas that match generated induction hypotheses and then integrating them into the statement soundness resume proof. E0006 shows only that one helper proof needs a better boundary at the ExtCall success suffix; it does not challenge the semantic invariant or type soundness statement.

#### Definition design
No semantic definitions change. Continue using local proof-boundary lemmas in `vyperTypeStmtSoundnessScript.sml` rather than unfolding interpreter internals at final integration sites.

#### Code structure
All edits remain in `semantics/prop/vyperTypeStmtSoundnessScript.sml`. This update adds/replaces only local ExtCall lemmas near the existing ExtCall proof infrastructure.

### C1.1: ExtCall expression soundness via standalone helper boundaries
- Kind: `proof_group`
- Risk: 2
- Work priority: 1
- Work units: 0
- Rationale: The stuck monolithic helper is decomposed into low-risk cleanup, successful-continuation boundary, and final helper leaves. C1.1.1 remains done and C1.1.3 remains the downstream consumer.
- Progress transition: `replacement`
- Carries progress/evidence from: C1.1.1, E0006
- Invalidates prior progress/evidence: old C1.1.2 monolithic proof route

#### Progress note
C1.1 is not abandoned; it is repaired by decomposing the failed C1.1.2 proof interface.

#### Summary
Repair the ExtCall helper path locally. Keep the proved update/tail bridge C1.1.1. Replace the old C1.1.2 monolithic proof with a successful-continuation boundary followed by the same final generated-IH helper. Preserve C1.1.3 as the later integration step once the final helper is proved.

#### Argument
The ExtCall evaluator splits into a prefix that evaluates arguments and checks calldata/account/run-call conditions, and a suffix that updates accounts/transient storage and handles return data or driver evaluation. Prefix failure branches are runtime errors and therefore type-sound immediately. Prefix success produces well-typed updated accounts via `run_ext_call_accounts_well_typed`; the argument IH gives a well-typed, env-consistent intermediate state. The common suffix is exactly the situation handled by the already proved C1.1.1 bridge once `get_tenv cx` is rewritten to `env.type_defs` and a return type value is obtained from `well_formed_type`.

#### Definition design
No new definitions. The proof interface for C1.1.2 must expose a lemma for the successful suffix after `run_ext_call`, hiding update simplification, `get_tenv` rewriting, `runtime_consistent` packaging, and the call to C1.1.1. Failure sign: if the final helper still manually instantiates C1.1.1 in static and nonstatic branches, the boundary is too weak.

#### Code structure
Keep all local ExtCall lemmas together in `semantics/prop/vyperTypeStmtSoundnessScript.sml`, near `update_accounts_transient_runtime_consistent`, `extcall_return_tail_sound`, `extcall_after_state_update_tail_sound`, and the argument-destination lemmas. Add the successful-continuation lemma before reintroducing `extcall_expr_sound_from_generated_ih`.

### C1.1.1: Bridge returned external-call state updates to the existing return-tail lemma
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 0
- Work units: 2
- Rationale: With the conclusion corrected to `Call ret_type ...`, this is a direct wrapper around proved local lemmas `update_accounts_transient_runtime_consistent` and `extcall_return_tail_sound`. The failed episode demonstrated the only blocker was the arbitrary `loc` variable.
- Supersedes: C1.1.1@wrong-loc-statement
- Progress transition: `replacement`
- Carries progress/evidence from: E0003
- Invalidates prior progress/evidence: C1.1.1 previous statement

#### Progress note
The previous C1.1.1 obligation is replaced because it was too general. E0003 remains useful evidence pinpointing the mismatch and justifying the corrected statement.

#### Summary
Prove a local bridge lemma for the ExtCall return tail after accounts/transient-storage update. The statement must use `Call ret_type (ExtCall stat (func_name,arg_types,ret_type)) es drv` in the result-typing conclusion. The proof should derive runtime consistency of the updated state using `update_accounts_transient_runtime_consistent`, then invoke `extcall_return_tail_sound`. This replaces the prior wrong arbitrary-`loc` helper statement.

#### Statement
Theorem extcall_after_state_update_tail_sound[local]:
  !env cx es stat func_name arg_types ret_type ret_tv drv returnData
   base_st accounts' tStorage' res st'.
    runtime_consistent env cx base_st /\ functions_well_typed cx /\
    accounts_well_typed accounts' /\
    well_typed_opt env drv /\
    evaluate_type env.type_defs ret_type = SOME ret_tv /\
    (!e. drv = SOME e ==> expr_type e = ret_type) /\
    (!env0 st0 res0 st0'.
       env_consistent env0 cx st0 /\ state_well_typed st0 /\
       context_well_typed cx /\ accounts_well_typed st0.accounts /\
       functions_well_typed cx /\ eval_expr cx (THE drv) st0 = (res0,st0') ==>
       (well_typed_expr env0 (THE drv) ==>
        state_well_typed st0' /\ env_consistent env0 cx st0' /\
        accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
        case res0 of INL tv => expr_result_typed env0 (THE drv) tv | INR _ => T)) /\
    (if returnData = [] /\ IS_SOME drv then eval_expr cx (THE drv)
     else do
       ret_val <- lift_sum_runtime (evaluate_abi_decode_return env.type_defs ret_type returnData);
       return (Value ret_val)
     od) (base_st with <| accounts := accounts'; tStorage := tStorage' |>) = (res,st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
    no_type_error_result res /\
    case res of
    | INL tv => expr_result_typed env (Call ret_type (ExtCall stat (func_name,arg_types,ret_type)) es drv) tv
    | INR _ => T

#### Approach
Start with `rpt gen_tac >> strip_tac`. First establish `runtime_consistent env cx (base_st with <|accounts := accounts'; tStorage := tStorage'|>)` by applying `update_accounts_transient_runtime_consistent` to the base runtime-consistency and `accounts_well_typed accounts'`. Then `irule extcall_return_tail_sound` with `fsig = (func_name,arg_types,ret_type)` and discharge premises by `simp[]`/the assumptions; there should be no goal mentioning a separate `loc`.

#### Not to try
Do not keep the old conclusion `Call loc ...`; the accepted stuck evidence proves that requires unavailable side conditions `ret_type = loc` and type evaluation at `loc`. Do not unfold `extcall_return_tail_sound` or the ABI decoder in this wrapper; if direct application does not line up, recheck the statement rather than doing evaluator-level proof search.

### C1.1.2: ExtCall generated-IH helper via successful-continuation boundary
- Kind: `proof_group`
- Risk: 2
- Work priority: 1
- Work units: 0
- Rationale: The old standalone helper proof required brittle low-level evaluator-tail plumbing. Splitting the successful continuation into its own lemma makes the final helper routine prefix case analysis plus two boundary applications.
- Dependencies: C1.1.1
- Supersedes: C1.1.2@E0006
- Progress transition: `replacement`
- Carries progress/evidence from: C1.1.1, E0006
- Invalidates prior progress/evidence: C1.1.2 previous monolithic proof attempt

#### Progress note
E0006's prefix exploration may guide case splits, but its monolithic tail proof is invalidated.

#### Summary
Replace the failed monolithic `extcall_expr_sound_from_generated_ih` proof with staged leaves. First remove the partial failed theorem block. Then prove one generic `extcall_success_continuation_sound` lemma for the common suffix after successful `run_ext_call`. Finally prove the original helper statement using evaluator prefix case analysis and the new continuation lemma. The final theorem name and statement stay unchanged for C1.1.3.

#### Description
E0006 is accepted as evidence that the old C1.1.2 proof interface was too coarse. The repair keeps the mathematical obligation but moves the fragile update/get_tenv/tail packaging into a small boundary lemma that matches both static and nonstatic success branches.

#### Statement
Final output remains the local theorem `extcall_expr_sound_from_generated_ih` with the same statement used in the failed attempt: it consumes the generated IH for `eval_exprs` on `es`, the generated IH for `eval_expr` on `THE drv`, and proves state/env/account/no-type-error plus typed result for `Call ret_type (ExtCall is_static (func_name,arg_types,ret_type)) es drv`.

#### Approach
Do not resume the failed proof at the C1.1.1 application site. Prove the continuation boundary first, then in the final helper step the evaluator only to the successful run-call branches and apply that boundary. Static/nonstatic branch-specific work should stop after extracting target/value and selecting `NONE` or `SOME amount`; all tail reasoning belongs to the continuation lemma.

#### Not to try
Do not continue adding manual `qexistsl`, `rewrite_tac[GSYM no_type_error_result_def]`, or broad `metis_tac` at the tail bridge site. Do not duplicate update/get_tenv/tail reasoning in static and nonstatic branches.

#### Argument
The final helper is true because the prefix and suffix obligations are separable. The prefix uses the args IH to type runtime argument values and preserve the intermediate state; argument-destination lemmas extract the concrete address/value needed by the evaluator. Failed prefix branches produce runtime errors. Successful prefix branches obtain well-typed updated accounts from `run_ext_call_accounts_well_typed` and then delegate the shared suffix to `extcall_success_continuation_sound`, which itself delegates to C1.1.1.

#### Definition design
The key proof interface is `extcall_success_continuation_sound`: its premises must match the evaluator fragment immediately after `run_ext_call` returned success. It should internally simplify `assert T`, account/transient updates, rewrite `get_tenv`, derive `evaluate_type ... = SOME ...` from `well_formed_type`, and apply `extcall_after_state_update_tail_sound`.

#### Code structure
All code goes in `semantics/prop/vyperTypeStmtSoundnessScript.sml`. Keep `env_consistent_get_tenv` if it already builds. Add `extcall_success_continuation_sound` before `extcall_expr_sound_from_generated_ih`; then add the final helper with the unchanged name.

### C1.1.2.0: Remove or revert the partial failed monolithic helper proof
- Kind: `source_cleanup`
- Risk: 1
- Work priority: 0
- Work units: 1
- Rationale: The source is not build-clean because the failed theorem proof is partial; removing it is mechanical.
- Carries progress/evidence from: E0006
- Invalidates prior progress/evidence: partial source edits from E0006 for extcall_expr_sound_from_generated_ih

#### Progress note
The failed source edits are evidence for cleanup and redesign, not proof progress to preserve.

#### Summary
Restore `vyperTypeStmtSoundnessScript.sml` around `extcall_expr_sound_from_generated_ih` so no unfinished failed proof remains. Keep already proved useful local helpers such as `env_consistent_get_tenv` if they build. Do not add cheats. This cleanup gates all new C1.1.2 proof work.

#### Description
Delete the failed theorem block from E0006 or replace it only when adding the new staged proof. The point is to stop trying to patch the non-closing monolithic script.

#### Approach
Edit only `semantics/prop/vyperTypeStmtSoundnessScript.sml`. Remove the partial `extcall_expr_sound_from_generated_ih` proof body from the E0006 attempt before beginning the new proof structure. Run a targeted check if available to catch syntax or unfinished-proof leftovers.

#### Not to try
Do not resume from line 9757 of the failed proof. Do not leave a `cheat`, `admit`, or unfinished theorem.

### C1.1.2.1: Boundary lemma for successful ExtCall suffix after account/transient updates
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 1
- Work units: 3
- Rationale: This isolates the formerly brittle tail-packaging fragment. The proof should be a small simplification of the suffix evaluator fragment followed by `env_consistent_get_tenv`, `evaluate_type_well_formed`, and C1.1.1.
- Dependencies: C1.1.1, C1.1.2.0
- Carries progress/evidence from: C1.1.1, E0006

#### Progress note
This extracts the exact tail-packaging subproblem identified by E0006 while reusing the proved C1.1.1 bridge.

#### Summary
Prove local lemma `extcall_success_continuation_sound`. It consumes the successful suffix evaluator equality after `run_ext_call` has returned `(T, returnData, accounts', tStorage')`. It proves the same state/env/account/no-type-error/typed-result conclusion for the ExtCall expression. It owns all update simplification, `get_tenv` rewriting, `runtime_consistent` packaging, and application of `extcall_after_state_update_tail_sound`.

#### Statement
Use this statement shape, adjusting bind syntax to what HOL accepts:
```sml
Theorem extcall_success_continuation_sound[local]:
  !env cx args_st accounts' tStorage' returnData res st'
    is_static func_name arg_types ret_type es drv.
    runtime_consistent env cx args_st /\ functions_well_typed cx /\
    accounts_well_typed accounts' /\ well_typed_opt env drv /\
    well_formed_type env.type_defs ret_type /\
    (!e. drv = SOME e ==> expr_type e = ret_type) /\
    (* same driver IH as in extcall_after_state_update_tail_sound *) /\
    (do
       _ <- assert T (Error (RuntimeError "ExtCall reverted"));
       _ <- update_accounts (K accounts');
       _ <- update_transient (K tStorage');
       if returnData = [] /\ IS_SOME drv then eval_expr cx (THE drv)
       else do
         ret_val <- lift_sum_runtime (evaluate_abi_decode_return (get_tenv cx) ret_type returnData);
         return (Value ret_val)
       od
     od) args_st = (res,st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    accounts_well_typed st'.accounts /\ no_type_error_result res /\
    case res of
    | INL tv => expr_result_typed env (Call ret_type (ExtCall is_static (func_name,arg_types,ret_type)) es drv) tv
    | INR _ => T
```

#### Approach
Simplify the `do` fragment with `assert_def`, `bind_def`, `return_def`, `update_accounts_def`, and `update_transient_def` until the premise is the exact tail expression evaluated at `args_st with <| accounts := accounts'; tStorage := tStorage' |>` except for `get_tenv cx`. From `runtime_consistent env cx args_st`, derive `env_consistent env cx args_st`; use `env_consistent_get_tenv` to rewrite `get_tenv cx` to `env.type_defs`. Use `evaluate_type_well_formed` on `well_formed_type env.type_defs ret_type` to obtain the `ret_tv` existential and then apply `extcall_after_state_update_tail_sound`.

#### Not to try
Do not include `run_ext_call`, target address, calldata, or static/nonstatic argument decoding in this lemma. Do not prove separate static and nonstatic suffix lemmas; the suffix is identical.

### C1.1.2.2: Reprove `extcall_expr_sound_from_generated_ih` using the continuation boundary
- Kind: `infrastructure_lemma`
- Risk: 2
- Work priority: 2
- Work units: 5
- Rationale: With the continuation boundary available, the remaining proof is evaluator prefix case analysis. Failure branches are runtime errors; success branches use `run_ext_call_accounts_well_typed` and then the boundary.
- Dependencies: C1.1.2.1
- Checkpoint: yes
- Progress transition: `replacement`
- Carries progress/evidence from: E0006, C1.1.2.1
- Invalidates prior progress/evidence: C1.1.2 previous monolithic proof attempt

#### Progress note
The obligation is unchanged, but the proof route is replaced; E0006's successful prefix exploration remains useful.

#### Summary
Prove the original standalone helper expected by C1.1.3. Reuse the failed attempt's prefix structure only: unfold `well_typed_expr` once, unfold `evaluate_def` once, split `eval_exprs`, apply args IH, split static/nonstatic and operational checks. In each successful branch, call `extcall_success_continuation_sound`. This checkpoint should leave C1.1.3 as a small integration step.

#### Description
The theorem name and statement must match the old planned helper so downstream integration does not change. This component should close C1.1.2 and unblock C1.1.3.

#### Statement
Same full statement as the failed attempt's `extcall_expr_sound_from_generated_ih`: it assumes runtime consistency premises, `functions_well_typed cx`, `well_typed_expr env (Call ret_type (ExtCall is_static (func_name,arg_types,ret_type)) es drv)`, the generated args IH, the generated driver IH, and the call evaluation equality; it concludes state/env/account preservation, `no_type_error_result res`, and typed result for the ExtCall expression.

#### Approach
Follow the prefix of E0006's proof until reaching `run_ext_call` success. Use `extcall_static_args_runtime_typed_dest` or `extcall_nonstatic_args_runtime_typed_dest` after the args IH gives `exprs_runtime_typed env es vs`. In success, prove `accounts_well_typed accounts'` by `run_ext_call_accounts_well_typed`; package `runtime_consistent env cx args_st` from `state_well_typed args_st`, `env_consistent env cx args_st`, and `context_well_typed cx`; then `irule extcall_success_continuation_sound`.

#### Not to try
Do not unfold the suffix updates or call C1.1.1 directly here. Avoid broad FOL/metis calls over the whole context; use the continuation boundary with small explicit premises. Do not split into separate final static/nonstatic helpers unless this revised component gets stuck again.

### C1.1.3: Integrate ExtCall Resume by applying the standalone helper
- Kind: `proof_refactor`
- Risk: 1
- Work priority: 20
- Work units: 3
- Rationale: After C1.1.2, the Resume should be analogous to the existing IntCall Resume tail: select two generated IH assumptions and apply the helper. The remaining place branch is a simple `well_typed_expr_def`/`type_place_expr` contradiction or simplification.
- Dependencies: C1.1.2
- Checkpoint: yes

#### Progress note
This closes the original C1.1 cheat once the helper is available.

#### Summary
Replace the `cheat` at `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall]` with a short proof. The expression half must only extract the generated args and driver IHs, then apply `extcall_expr_sound_from_generated_ih`. The place half should be discharged by the call/place typing simplification already used in neighboring Resume proofs.

#### Statement
```sml
Resume eval_all_type_sound_mutual[Expr_Call_ExtCall]:
  ...
QED
```
No new theorem statement: this proves the existing suspended mutual theorem branch.

#### Approach
Use the IntCall Resume pattern near lines 16790--16820 as the template, but only name two assumptions: `actual_ih` for `eval_exprs cx es` and `driver_ih` for `eval_expr cx (THE drv)`. In the expression conjunct, after `strip_tac`, apply `extcall_expr_sound_from_generated_ih` and solve premises with `MATCH_ACCEPT_TAC` for the named IHs or `first_assum ACCEPT_TAC`. For the place conjunct, `rpt strip_tac` and simplify with `Once well_typed_expr_def`/`type_place_expr` as in the `Send`/`RawLog` completed branches.

#### Not to try
Do not unfold `evaluate_def` in this Resume. Do not repeat the failed prefix-stepping proof. If the helper statement does not unify without manual quoted assumptions or long theorem plumbing, stop and report a helper-interface mismatch rather than patching the Resume.

### C1.2: RawCallTarget expression-soundness helper and Resume integration
- Kind: `proof_group`
- Risk: 2
- Work priority: 10
- Work units: 0
- Rationale: Carried forward as the parent for C1.2.1. The subtree remains standard once its strict prerequisites are available; the current repair ensures the only RawCallTarget proof leaf cannot be scheduled before those prerequisites close.
- Progress transition: `carry_forward`
- Carries progress/evidence from: C1.2

#### Progress note
Included only to satisfy dotted-component parent requirements; the C1.2 strategy is unchanged except for the child dependency repair.

#### Summary
Parent context for the RawCallTarget expression-soundness helper and Resume integration. The substantive work remains in C1.2.1. The dependency repair below makes `C1.2.1` wait for the concrete ExtCall terminal checkpoint and C2.1.

#### Argument
RawCallTarget soundness should mirror the other call-expression branches: first prove a local expression helper using the generated argument-evaluation IH, raw-call branch facts, and the well-formedness theorem for `raw_call_return_type`; then make the Resume proof a short wrapper. The well-formedness arithmetic for return types is not part of this subtree and is imported from C2.1.

#### Definition design
No definition changes are expected. The proof interface boundary is `raw_call_target_expr_sound[local]`: it should consume the live Resume assumptions and return the exact preservation/no-type-error/result-typing facts needed by the mutual theorem branch. A failure sign is needing to unfold `raw_call_return_type_def` or word-size arithmetic here, which means C2.1 has not supplied the intended boundary theorem.

#### Code structure
Place `raw_call_target_expr_sound[local]` in `semantics/prop/vyperTypeStmtSoundnessScript.sml` immediately before `Resume eval_all_type_sound_mutual[Expr_Call_RawCallTarget]`. Replace only the RawCallTarget Resume cheat in this component; do not edit builtin return-type proof code here.

### C1.2.1: Prove `raw_call_target_expr_sound` and close the RawCallTarget Resume after ExtCall and return-type prerequisites
- Kind: `proof`
- Risk: 2
- Work priority: 90
- Work units: 3
- Rationale: The proof obligation is unchanged and remains standard local expression-branch work once its real prerequisites are available. The previous metadata-only dependency repair did not affect the scheduler frontier, so this replacement additionally gives the leaf a late local work priority. This is a scheduling repair, not a proof-strategy change: C1.2.1 must not be selected until the ExtCall terminal branch and raw-call return type well-formedness are closed.
- Dependencies: C1.1.3, C2.1
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: C1.2.1, TO_type_system_rewrite-20260531T201607Z_m0074_t001, TO_type_system_rewrite-20260531T201607Z_m0075_t001

#### Progress note
Same RawCallTarget proof obligation as before; no proof progress is discarded. This refinement repairs a PLAN/frontier contradiction by combining the intended semantic dependencies with a late priority so C1.2.1 is not selected ahead of its queued prerequisites.

#### Summary
- Add local helper `raw_call_target_expr_sound[local]` before the RawCallTarget Resume.
- This leaf is intentionally scheduled late (`work_priority=90`) because dependency metadata alone did not stop premature selection in the current harness.
- Do not begin this component while `C1.1.2`, `C1.1.3`, or `C2.1` remain queued/not done; the next valid frontier work should be one of those prerequisite leaves.
- Use generated IHs for raw-call argument evaluation and existing raw-call argument/tail lemmas.
- Use `raw_call_return_type_well_formed` from C2.1 when result typing/well-formedness of the raw-call return type is needed.
- Replace the `cheat` in `Resume eval_all_type_sound_mutual[Expr_Call_RawCallTarget]` with a short wrapper proof, and close the place-expression conjunct by simplification from `well_typed_expr_def`.

#### Description
This component owns only the RawCallTarget expression helper and the corresponding suspended mutual-theorem branch. It must not absorb ExtCall work or the arithmetic/type-formation proof for raw-call return types. The scheduler repair is part of this replacement: semantic dependencies remain `C1.1.3` and `C2.1`, and the local priority is now deliberately later than the prerequisite call-expression leaves so the executor is not instructed to begin RawCallTarget prematurely.

#### Statement
Suggested local theorem shape, to be specialized to the actual Resume assumptions:
```sml
Theorem raw_call_target_expr_sound[local]:
  (* env/cx/st consistency and generated IH assumptions *) /\
  well_typed_expr env (Call (raw_call_return_type flags) (RawCallTarget flags) es NONE) /\
  eval_expr cx (Call (raw_call_return_type flags) (RawCallTarget flags) es NONE) st = (res,st')
  ==>
  state_well_typed st' /\ env_consistent env cx st' /\
  accounts_well_typed st'.accounts /\ no_type_error_result res /\
  (case res of
   | INL tv => expr_result_typed env (Call (raw_call_return_type flags) (RawCallTarget flags) es NONE) tv
   | INR _ => T)
```
If the actual mutual theorem uses a location/type variable `loc`, extract `loc = raw_call_return_type flags` from `well_typed_expr_def` before invoking the helper rather than adding a second annotation parameter.

#### Approach
Only after `C1.1.3` and `C2.1` are done, unfold `well_typed_expr_def` once to extract `drv = NONE`, the return-type equality, argument length/types, and `flags.rcf_max_outsize < dimword(:256)`. Unfold `evaluate_def` once for the RawCallTarget branch, split on `eval_exprs cx es st`, and apply the generated IH to the argument evaluation result; error branches close via `no_type_error_result_def`. In the successful path, use raw-call argument destructors/tail soundness lemmas already available in the script, and invoke `raw_call_return_type_well_formed` rather than unfolding its definition.

#### Not to try
Do not begin this component while `C1.1.2`, `C1.1.3`, or `C2.1` is queued. Do not rely on the scheduler's dependency enforcement alone for this leaf; if it is still Oracle-next before those prerequisites close after this replacement, stop again and request ancestor-level frontier repair. Do not unfold `raw_call_return_type_def`, `type_slot_size_def`, or `word_size` arithmetic in this component; that obligation belongs to C2.1. Do not write a long inline Resume proof; if the wrapper needs extensive evaluator/tail reasoning, move that reasoning into `raw_call_target_expr_sound` with a conclusion matching the Resume use site.

### C1.3: Focused statement-soundness build and cheat audit
- Kind: `build_audit`
- Risk: 1
- Work priority: 20
- Work units: 1
- Rationale: Mechanical audit after the two statement branches. Any failure gives concrete next-theorem evidence; no design work is expected in this leaf.
- Dependencies: C1.1, C1.2
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: C2.8

#### Summary
- Run `holbuild build vyperTypeStmtSoundnessTheory`.
- Confirm the ExtCall and RawCallTarget resumes are build-clean.
- Confirm no new `cheat`, `suspend`, or probe fragment was introduced in the statement-soundness file.
- If the build advances to another theorem, record the exact location for final validation or escalation.

#### Statement
```sh
holbuild build vyperTypeStmtSoundnessTheory
```

#### Approach
Use the normal project build path. Inspect warnings, not only errors. If a failure is outside the two call-target branches, do not start repairing it unless it is a strict prerequisite for the current build and falls under the task scope; otherwise escalate with exact evidence.

#### Not to try
Do not treat a partial compile through the helper theorem as this audit passing if the Resume still fails. Do not broaden into unrelated assignment/builtin work from this component.

### C2: Builtin/raw-call prerequisite support
- Kind: `proof_group`
- Risk: 2
- Work priority: 20
- Work units: 0
- Rationale: The current migrated plan identifies `raw_call_return_type_well_formed` as the remaining builtin-file cheat. Its proof is localized arithmetic/case analysis over `raw_call_return_type_def`, not an evaluator proof.
- Required for completion: yes
- Dependencies: C0
- Progress transition: `refinement`
- Carries progress/evidence from: C4.5

#### Summary
- Close the reachable `raw_call_return_type_well_formed` cheat in `vyperTypeBuiltinsScript.sml`.
- Audit only same-layer Env/MsgGas support if current source still contains a reachable cheat needed by `vyperSemanticsHolTheory`.
- Keep this as builtin/type support; statement-call proofs consume the resulting boundary.
- Do not duplicate raw-call evaluator reasoning in statement proofs.

#### Approach
First prove raw-call well-formedness, then run the builtin theory build. Only after that audit for same-layer reachable Env/MsgGas cheats if the build/CHEAT warning still reports them.

#### Not to try
Do not unfold statement or raw-call expression evaluators here. Do not weaken current public builtin statements to avoid arithmetic. Do not edit outside `semantics/prop`.

#### Argument
Raw-call return well-formedness is a finite case/arithmetic fact. After unfolding `raw_call_return_type_def`, `well_formed_type_def`, `evaluate_type_def`, and `type_slot_size_def`, the only nontrivial branch is the dynamic bytes/output-size bound. The hypothesis `flags.rcf_max_outsize < dimword(:256)` and the existing `word_size_le`/`word_size` facts should imply the required slot-size bound. Env/MsgGas support, if still reachable, is constructor-specific builtin typing, not a semantic evaluation argument.

#### Definition design
No definitions should change. The exported interface is the existing theorem name `raw_call_return_type_well_formed`. For Env/MsgGas, preserve existing theorem premises; in particular do not remove an `item <> MsgGas` premise unless a checked current statement requires and proves it. Failure sign: a statement-soundness proof unfolding `raw_call_return_type_def` because this boundary is unavailable.

#### Code structure
All C2 edits belong in `semantics/prop/vyperTypeBuiltinsScript.sml`, near `raw_call_return_type_well_formed` and adjacent raw-call/Env support lemmas. Keep any new arithmetic helper local unless downstream files explicitly need it.

### C2.1: Prove `raw_call_return_type_well_formed`
- Kind: `proof`
- Risk: 2
- Work priority: 0
- Work units: 3
- Rationale: Localized arithmetic over existing definitions. The plan has a known proof route using `word_size_le` and case splits over the flags/return-type shape.
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: C4.5

#### Summary
- Replace the cheat in `raw_call_return_type_well_formed`.
- Use `word_size_le`, `word_size`, `type_slot_size_def`, and the `flags.rcf_max_outsize < dimword(:256)` hypothesis.
- Keep any arithmetic helper near the raw-call theorem.
- Build `vyperTypeBuiltinsTheory` after the edit.

#### Statement
```sml
Theorem raw_call_return_type_well_formed:
  flags.rcf_max_outsize < dimword(:256) ==>
  well_formed_type tenv (raw_call_return_type flags)
```

#### Approach
Unfold `raw_call_return_type_def`, `well_formed_type_def`, `evaluate_type_def`, and `type_slot_size_def` in a controlled case split over `flags`/return-shape branches. Derive `word_size n <= n` from `word_size_le`, split on the comparison branch involving `word_size`, and close the natural-number/dimword inequalities with arithmetic.

#### Not to try
Do not push this arithmetic obligation into `RawCallTarget` statement soundness. Do not unfold raw-call evaluator semantics or ABI return decoding here.

### C2.2: Audit/close same-layer reachable Env/MsgGas builtin support if still reported
- Kind: `source_audit`
- Risk: 1
- Work priority: 10
- Work units: 1
- Rationale: This is conditional mechanical audit after raw-call well-formedness. It only becomes proof work if current build/CHEAT output reports a reachable Env/MsgGas support cheat in the builtin layer.
- Dependencies: C2.1
- Progress transition: `refinement`
- Carries progress/evidence from: C4.5

#### Summary
- Grep/audit `vyperTypeBuiltinsScript.sml` for remaining reachable Env/MsgGas cheats after C2.1.
- If none are reported by the build path, close as no-op.
- If one is reported, prove it by constructor rewriting with the existing premises.
- Escalate if the current theorem would require dropping a known necessary `item <> MsgGas` premise.

#### Statement
Conditional obligation: any same-layer reachable Env/MsgGas support theorem in `vyperTypeBuiltinsScript.sml` that still contains `cheat`/suspended proof text and is required by `vyperSemanticsHolTheory`.

#### Approach
Use the focused build/CHEAT output to decide whether this leaf has proof work. For a real Env/MsgGas support theorem, unfold only the relevant builtin/env item typing definitions and split constructors; preserve side conditions from the source theorem.

#### Not to try
Do not plan a repository-wide Env builtin cleanup. Do not remove `item <> MsgGas` from generic helpers as a convenience.

### C2.3: Focused builtin build and cheat audit
- Kind: `build_audit`
- Risk: 1
- Work priority: 20
- Work units: 1
- Rationale: Mechanical verification after builtin edits. Any remaining warning gives exact evidence for a small follow-up replan.
- Dependencies: C2.1, C2.2
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: C4.5

#### Summary
- Run `holbuild build vyperTypeBuiltinsTheory`.
- Confirm `raw_call_return_type_well_formed` is build-clean.
- Confirm no reachable builtin-layer CHEAT remains in current source.
- Record exact next failure if the build advances beyond builtin support.

#### Statement
```sh
holbuild build vyperTypeBuiltinsTheory
```

#### Approach
Use `holbuild`, not direct HOL. Inspect CHEAT warnings and source locations. If a failure is unrelated to raw-call/Env/MsgGas reachable support, escalate rather than broadening the task.

#### Not to try
Do not use this audit to start ABI/default theorem cleanup unless the current build proves it is a reachable prerequisite.

### C3: Call wrapper and public fresh soundness surface carry-forward/audit
- Kind: `proof_group`
- Risk: 1
- Work priority: 30
- Work units: 0
- Rationale: The migrated plan's current progress note says the build has narrowed to three remaining cheats before final validation. Therefore call wrappers and public surface are treated as carried-forward unless final validation identifies a concrete reachable regression.
- Required for completion: yes
- Dependencies: C1.3, C2.3
- Progress transition: `carry_forward`
- Carries progress/evidence from: C5, C6, old C5.1, old C5.2, old C5.3, old C6.1

#### Summary
- Preserve completed call-wrapper and public-wrapper work as carried evidence.
- Do not schedule old wrapper subtrees unless a current build reports them as failing/reachable cheats.
- The final validation C4 remains the authority for whether these wrappers are truly clean.
- If a wrapper regression appears, escalate with exact theorem name rather than starting a broad public-surface rewrite.

#### Approach
Treat as already done unless C4 validation reports a current source failure. Do not begin this parent directly.

#### Not to try
Do not reopen old call-wrapper or public-wrapper proofs proactively. Do not use retired old-stack theories to prove fresh public wrappers.

#### Argument
Public and call-wrapper theorems are projections of completed subsystem invariants. Once statement-call branches and raw-call builtin support are closed, no fresh induction should be needed in wrapper files. This group exists only to keep the task-critical dependency path explicit without reauthorizing stale proof work.

#### Definition design
No definitions change. Wrapper interfaces should remain existing public names/strengths. Failure sign: a wrapper proof unfolding evaluator definitions instead of projecting a completed joint theorem.

#### Code structure
No edits are planned under C3. If final validation exposes a wrapper regression, edits would belong in `vyperTypeCallSoundnessScript.sml` or `vyperTypeSoundnessNewScript.sml` only, and require a new scoped plan update.

### C4: Final `vyperSemanticsHolTheory` zero-CHEAT validation
- Kind: `validation`
- Risk: 1
- Work priority: 40
- Work units: 3
- Rationale: Mechanical final build/audit after the remaining focused proofs. Remaining warnings, if any, will be concrete and should drive a narrowly scoped follow-up plan.
- Required for completion: yes
- Dependencies: C1.3, C2.3, C3
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: old C7

#### Summary
- Run `holbuild build vyperSemanticsHolTheory`.
- Confirm zero CHEAT warnings reachable from `vyperSemanticsHolTheory`.
- Confirm no temporary probes, `suspend`, or `cheat` text remains in edited task files.
- If warnings remain, identify exact reachable theory/theorem and stop for a focused replan.
- Respect repository hygiene: only task-owned files under `semantics/prop`; do not GPG-sign commits.

#### Statement
```sh
holbuild build vyperSemanticsHolTheory
```
The build must succeed with zero CHEAT warnings reachable from `vyperSemanticsHolTheory`.

#### Approach
Run the task-required build after C1 and C2 focused audits pass. Inspect CHEAT warnings and dependency reachability; distinguish old retired theories from the fresh stack imported by `vyperSemanticsHolTheory`. If committing progress, use an explicit non-GPG-signed commit command/config and stage narrowly selected files.

#### Not to try
Do not use direct HOL as the final validation. Do not stage unrelated tracked diffs or untracked scratch files. Do not continue repairing unexpected failures without escalation; the task explicitly says to stop on unexpected tooling or design issues.
