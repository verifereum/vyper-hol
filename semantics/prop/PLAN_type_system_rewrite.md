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

### C1: Statement soundness: remaining non-internal call-target expression branches
- Kind: `proof_group`
- Risk: 2
- Work priority: 10
- Work units: 0
- Rationale: Carried forward unchanged as the required parent context for updating C1.2. The local C1.2 scheduling repair does not alter the broader C1 strategy.
- Required for completion: yes
- Progress transition: `carry_forward`
- Carries progress/evidence from: C1

#### Progress note
Included solely because the PLAN schema requires explicit parents for dotted components. No executable work or sibling scheduling under C1 is changed by this C1.2-scoped update.

#### Summary
- Parent context carried forward only to satisfy dotted component structure.
- The substantive update is confined to C1.2 and C1.2.1.
- C1 remains the statement-soundness group for remaining non-internal call-target expression branches.
- No sibling strategy is changed by this merge.

### C1.1: ExtCall expression soundness via standalone helper boundaries
- Kind: `proof_group`
- Risk: 2
- Work priority: 10
- Work units: 0
- Rationale: The prior risk was caused by the arbitrary `loc` annotation in C1.1.1. Source facts show ExtCall well-typedness enforces `ty = ret_ty`, and `extcall_return_tail_sound` already concludes typing for `Call ret_type ...`; after aligning the helper interface to that invariant, the subtree is standard helper composition.
- Progress transition: `refinement`
- Carries progress/evidence from: C1.1, E0002, E0003

#### Progress note
E0002 still supports standalone helpers. E0003 is accepted as evidence that the first helper statement was too general; this refinement repairs the annotation invariant while preserving the strategy.

#### Summary
- Prove the ExtCall Resume through standalone local helpers, not by unfolding the evaluator inside the Resume.
- The key interface invariant is: for `ExtCall _ (_,arg_types,ret_type)`, the call expression annotation is the same `ret_type`.
- C1.1.1 bridges post-external-call account/storage updates into `extcall_return_tail_sound`.
- C1.1.2 packages the generated argument-IH and optional-driver-IH context into a standalone ExtCall expression soundness helper.
- C1.1.3 should then be a short Resume refactor applying C1.1.2.

#### Approach
Rebase the subtree around the source invariant `ty = ret_ty` for ExtCall. The standalone helper statements should use the return type from the external function signature as both the ABI decode type and the expression annotation. This avoids arbitrary-annotation side conditions and lets `irule extcall_return_tail_sound` solve the tail result typing directly.

#### Not to try
Do not prove or assume `loc = ret_type` after the fact for an arbitrary `loc`; the failed episode showed HOL correctly generates that impossible obligation. Do not unfold the full ExtCall evaluator inside the Resume again; prior evidence showed that route creates timeout-prone large goals.

#### Argument
The ExtCall well-typedness definition has `well_typed_expr env (Call ty (ExtCall _ (_,arg_types,ret_ty)) args drv)` requiring `ty = ret_ty`. Therefore every soundness conclusion for an ExtCall result should mention `Call ret_type (ExtCall stat (func_name,arg_types,ret_type)) es drv`, not `Call loc ...` for an unrelated annotation. The existing local lemma `extcall_return_tail_sound` is exactly the tail boundary: once the post-call tail computation is run from a runtime-consistent state, it proves state/env/accounts preservation, no type error, and result typing for `Call ret_type (ExtCall stat fsig) es drv`.

#### Definition design
No new definitions are needed. Use two boundary facts: `update_accounts_transient_runtime_consistent`, already present, and the repaired C1.1.1 bridge whose conclusion uses `Call ret_type ...`. Failure sign: any remaining goal demanding `ret_type = loc`, `evaluate_type ... loc`, or ABI decoding at `loc` means the statement still has the wrong annotation variable.

#### Code structure
All edits stay in `semantics/prop/vyperTypeStmtSoundnessScript.sml`. Place C1.1.1 immediately after `extcall_return_tail_sound` and before the ExtCall argument destination helpers, so C1.1.2 can use it locally. Do not change `well_typed_expr_def`; the required equality is already in the imported definition.

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

### C1.1.2: Prove the standalone ExtCall expression helper from generated IHs
- Kind: `infrastructure_lemma`
- Risk: 2
- Work priority: 10
- Work units: 5
- Rationale: The helper remains standard once it depends on the corrected tail bridge. Its final result typing must also use the external return type as the call annotation, matching ExtCall well-typedness.
- Dependencies: C1.1.1
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: C1.1.2, E0002, E0003

#### Progress note
This is the same standalone-helper obligation planned after E0002, refined to consume the corrected C1.1.1 interface and avoid the wrong arbitrary annotation.

#### Summary
Package the live ExtCall Resume context into a standalone helper. Use the argument-IH to obtain runtime-typed evaluated arguments and no type errors, and use the optional-driver IH only in the return-tail branch. The helper conclusion should type `Call ret_type (ExtCall stat (func_name,arg_types,ret_type)) es drv`, not an arbitrary annotation. C1.1.1 supplies the tail bridge after account/transient-storage updates.

#### Statement
State the standalone ExtCall expression soundness helper with the same parameters and assumptions needed by the live Resume context, but ensure the ExtCall expression in the conclusion is `Call ret_type (ExtCall stat (func_name,arg_types,ret_type)) es drv`. Include the usual runtime/context/functions consistency assumptions, `well_typed_expr env (Call ret_type (ExtCall stat (func_name,arg_types,ret_type)) es drv)`, the generated expression-list IH for `es`, and the optional-driver IH for `drv`. The conclusion should match the expression-soundness shape needed by the Resume: preservation of state/env/accounts, no type error, and `expr_result_typed` for successful results.

#### Approach
Prove this outside the Resume by case-splitting the evaluated arguments and static/nonstatic ExtCall shape only as much as necessary to obtain `returnData`, updated accounts, and updated transient storage. After the external-call step, invoke C1.1.1 for the return tail. Use `well_typed_expr_def` only to extract `ty = ret_type`, `MAP expr_type es = arg_types`, and the driver type condition; do not leave a separate call-annotation variable in the theorem.

#### Not to try
Do not resurrect the inline Resume proof or broad `gvs[]` over evaluator internals; that was the source of the earlier risk mismatch. Do not formulate this helper with `Call loc ...` unless there is an explicit hypothesis `loc = ret_type` from the live context; current source indicates the cleaner statement is to use `ret_type` directly.

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
- Rationale: The proof remains standard once its strict prerequisites are available, but C1.2 must not be a directly executable leaf while C1.1 and C2.1 are still queued. The subtree is now decomposed so the only executable RawCallTarget proof leaf depends explicitly on those prerequisites.
- Dependencies: C1.1, C2.1
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: C1.2

#### Progress note
This is a scheduling/decomposition refinement of the same RawCallTarget obligation. No proof progress is invalidated because no C1.2 edits were made; the update only prevents premature execution before C1.1 and C2.1.

#### Summary
- C1.2 is a gated proof group, not an immediately editable leaf.
- Do not work on RawCallTarget statement soundness until the repaired C1.1 helper stack and C2.1 `raw_call_return_type_well_formed` are proved.
- After those prerequisites, prove a local `raw_call_target_expr_sound` boundary theorem and use it to close `Resume eval_all_type_sound_mutual[Expr_Call_RawCallTarget]`.
- The RawCallTarget branch should use existing raw-call/builtin boundaries, not duplicate C2.1 arithmetic.
- This update repairs only C1.2 scheduling/dependency metadata; it does not re-plan C1.1 or C2.1.

#### Description
The earlier C1.2 leaf was beginable even though its own plan declared dependencies on C1.1 and C2.1. That was unsafe because the RawCallTarget proof needs the raw-call return type well-formedness boundary and should not reproduce its arithmetic locally. Treat C1.2 as a grouping/checkpoint node and place the actual proof work in C1.2.1, which is dependency-gated on the external prerequisites.

#### Approach
Wait for C1.1 and C2.1 to close before editing the RawCallTarget Resume. Once available, prove the local helper first, then replace the Resume cheat with a short application of that helper and simplification for the place-expression conjunct.

#### Not to try
Do not start editing `Resume eval_all_type_sound_mutual[Expr_Call_RawCallTarget]` while `raw_call_return_type_well_formed` still contains a cheat. Do not inline or reprove the raw-call return-type arithmetic in `vyperTypeStmtSoundnessScript.sml`; that proof belongs to C2.1 in `vyperTypeBuiltinsScript.sml`. Do not use this scheduling repair as a reason to modify C1.1 or C2.1 from inside the C1.2 subtree.

#### Argument
For RawCallTarget, `well_typed_expr env (Call ty (RawCallTarget flags) args drv)` supplies the exact return annotation `ty = raw_call_return_type flags`, `drv = NONE`, `LENGTH args = 3`, argument types `(address, bytes bd, uint256)`, and the bound `flags.rcf_max_outsize < dimword(:256)`. The expression-soundness proof first uses the generated IH for `eval_exprs` to obtain runtime typing and preservation after argument evaluation. In the successful argument path, raw-call target argument destructors and tail/result lemmas establish state preservation, absence of `TypeError`, and result typing for the call. The return value type is well-formed only via `raw_call_return_type_well_formed`, so that theorem is a strict prerequisite rather than something to unfold in the statement-soundness script.

#### Definition design
No definition changes are planned. The proof interface for this subtree is a single local boundary helper whose assumptions match the live Resume context after unfolding `well_typed_expr_def` once and `evaluate_def` once for the RawCallTarget branch. Failure signs: the helper goal asks to prove arithmetic facts about `word_size`/`dimword`; the proof repeatedly unfolds `raw_call_return_type_def`; or the Resume grows evaluator-tail reasoning instead of just applying the helper.

#### Code structure
All C1.2 edits, after dependencies close, belong in `semantics/prop/vyperTypeStmtSoundnessScript.sml`. Put `raw_call_target_expr_sound[local]` near analogous expression-call helpers and before `Resume eval_all_type_sound_mutual[Expr_Call_RawCallTarget]`. Do not edit `vyperTypeBuiltinsScript.sml` under C1.2; that file is owned by C2.1 for this prerequisite.

### C1.2.1: Prove `raw_call_target_expr_sound` and close the RawCallTarget Resume
- Kind: `proof`
- Risk: 2
- Work priority: 0
- Work units: 3
- Rationale: After C1.1 and C2.1 are available, this is local expression-branch proof work mirroring established call-branch structure. The only nonlocal arithmetic/type-formation obligation is explicitly imported through C2.1.
- Dependencies: C1.1, C2.1
- Checkpoint: yes

#### Progress note
New child leaf created to make the existing C1.2 obligation dependency-gated and non-leaf at the parent level.

#### Summary
- Add local helper `raw_call_target_expr_sound[local]` before the RawCallTarget Resume.
- Use generated IHs for argument evaluation and existing raw-call argument/tail lemmas.
- Use `raw_call_return_type_well_formed` from C2.1 when result typing/well-formedness of the raw-call return type is needed.
- Replace the `cheat` in `Resume eval_all_type_sound_mutual[Expr_Call_RawCallTarget]` with a short wrapper proof.
- Close the place-expression conjunct by simplification from `well_typed_expr_def`.

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
Unfold `well_typed_expr_def` once to extract `drv = NONE`, the return-type equality, argument length/types, and `flags.rcf_max_outsize < dimword(:256)`. Unfold `evaluate_def` once for the RawCallTarget branch, split on `eval_exprs cx es st`, and apply the generated IH to the argument evaluation result; error branches close via `no_type_error_result_def`. In the successful path, use raw-call argument destructors/tail soundness lemmas already available in the script, and invoke `raw_call_return_type_well_formed` rather than unfolding its definition.

#### Not to try
Do not prove this before C2.1 is closed. Do not unfold `raw_call_return_type_def`, `type_slot_size_def`, or `word_size` arithmetic in this component. Do not write a long inline Resume proof; if the wrapper needs extensive evaluator/tail reasoning, move that reasoning into `raw_call_target_expr_sound` with a conclusion matching the Resume use site.

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
