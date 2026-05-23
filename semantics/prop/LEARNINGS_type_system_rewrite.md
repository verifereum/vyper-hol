# LEARNINGS_type_system_rewrite

Reusable proof patterns only. Greppable structured entries; evidence refs point to episodes/tool outputs/source.

## L0315 scope='global' tags=env.type_defs,drule,bridging
shape: env.type_defs vs get_tenv cx mismatch blocking drule/irule
pattern: When fs[] rewrites env.type_defs->get_tenv cx, lemmas using env.type_defs won't match. Fix: derive env.type_defs form via metis_tac before fs[], OR use get_tenv cx form after fs[], OR single fs[all_needed_lemmas] may chain before elimination.
works_when: Applying typing lemmas after fs/gvs rewrites env.type_defs to get_tenv cx
evidence:
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:631-660

## L0316 scope='global' tags=metis_tac,boundary_lemma
shape: metis_tac vs drule/irule for boundary lemmas with many variables
pattern: For boundary lemmas with 5+ antecedents matching assumptions: use metis_tac[boundary_lemma]. metis handles assumption matching and existential resolution automatically.
works_when: Goal is no_type_error_result and boundary lemma has right conclusion with many antecedents
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2407-2451

## L0317 scope='global' tags=lookup_global,contradiction
shape: lookup_global result shape constrains var_decl_info constructor
pattern: Contradiction lemmas: lookup_global_Value_not_HashMapVarDecl, lookup_global_ArrayRef_not_StorageVarDecl, lookup_global_HashMapRef_not_StorageVarDecl. Proof: mp_tac equation >> simp[lookup_global_def, bind_def, lift_option_type_def, return_def, raise_def, AllCaseEqs(), var_decl_info_CASE_rator, prod_CASE_rator, option_CASE_rator, type_value_CASE_rator, toplevel_value_CASE_rator, LET_THM] >> rpt strip_tac >> gvs[].
works_when: Proving contradiction between lookup_global result shape and find_var_decl type
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1262-1318

## L0318 scope='global' tags=resolve_array_element,TypeError,ArrayTV
shape: resolve_array_element TypeError unreachable under typed target path through ArrayTV
pattern: resolve_array_element cannot return INR(TypeError) when subscripts at ArrayTV levels are all ValueSubscript(IntV _). target_path_step_type on Type(ArrayT ...) forces this. Prove resolve_array_element_no_type_error via ho_match_mp_tac resolve_array_element_ind; use qspec_then 0/1 for elem_offset.
works_when: Proving no-TypeError results for code paths through resolve_array_element where target_path_type constrains subscripts
evidence:
- source:semantics/vyperStateScript.sml:833-834
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:269-270

## L0350 scope='global' tags=holbuild,pairarg_tac,FIRST_ABSAM,instrumentation
shape: holbuild FIRST_ABSAM instrumentation assertion from pairarg_tac
pattern: In holbuild, pairarg_tac triggers FIRST_ABSAM instrumentation assertion in new proofs. Replace with Cases_on `p` >> gvs[] (where p is the pair variable). This avoids FIRST_ABSAM and produces equivalent pair destructuring. fs[] also works to expand definitions in assumptions where gvs[] does not.
works_when: Building new theorems with holbuild where pair destructuring or definition expansion in assumptions is needed and FIRST_ABSAM/disch_then instrumentation assertions fire
evidence:
- tool_output:TO_type_system_rewrite-20260515T192259Z_m11231_t001
- tool_output:TO_type_system_rewrite-20260515T192259Z_m11233_t001

## L0424 scope='global' tags=existential,PULL_EXISTS,rename1,API_corruption
shape: Proving subgoals with existentially-quantified variables from assumptions
pattern: When an assumption like expr_runtime_typed env e tvl contains ?tv. evaluate_type ... = SOME tv /\ ..., do NOT try to prove evaluate_type ... = SOME tv as a subgoal with a free variable tv. Instead: gvs[expr_runtime_typed_def, PULL_EXISTS] to expose the existential, then rename1 to give the witness a stable name. This avoids the API /\ corruption issue and avoids type-mismatch failures from free vs bound variables.
works_when: Assumptions contain existentially quantified facts that need to be unfolded and the witness variables need stable names for subsequent drule/irule calls.
evidence:
- tool_output:TO_type_system_rewrite-20260515T192259Z_m12630_t001

## L0450 scope='global' tags=
shape: type_value constructor order: BaseTV, TupleTV, ArrayTV, StructTV, FlagTV, NoneTV
pattern: Cases_on on type_value creates 6 subgoals in definition order: BaseTV first, ArrayTV third. Use explicit case labels or >~ [ArrayTV pattern] for targeted dispatch.
works_when: Cases_on root_tv where need different strategies for ArrayTV vs non-ArrayTV
evidence:
- source:semantics/vyperValueScript.sml:11-19
- tool_output:TO_type_system_rewrite-20260515T192259Z_m13481_t001

## L0504 scope='global' tags=API_corruption,Definition,Unicode,wedge,workaround,multi-clause
shape: HOL4 Definition with conjunction between equations
pattern: Use Unicode ∧ (U+2227) instead of ASCII /\ between Definition equations. HOL4 accepts Unicode logical connectives. The Anthropic API corrupts /\ to /| in tool call content. Multi-clause definition: `(f cx (C1 ...) = ...) ∧ (f cx (C2 ...) = ...) ∧ ... End`. This gives per-constructor rewrite rules for simp, unlike single-equation case expressions which cause simp to loop on recursive calls.
works_when: Writing new HOL4 Definition with multiple pattern-matching clauses joined by conjunction
evidence:
- tool_output:TO_type_system_rewrite-20260516T092459Z_m14906_t001

## L0505 scope='global' tags=ETA_AX,EVERY,eta-expansion,simp
shape: simp produces eta-expanded lambda in EVERY/MLIST goal
pattern: When simp[def] produces a goal like `EVERY (λa. f cx a) gvs ⇔ EVERY (f cx) gvs` (eta-expanded vs point-free), use `metis_tac[ETA_AX]` to close the gap. simp alone cannot normalize this.
works_when: Biconditional or equational goal where one side has an eta-expanded lambda and the other is point-free
evidence:
- tool_output:TO_type_system_rewrite-20260516T092459Z_m14902_t001

## L0588 scope='global' tags=irule,metis_tac,universal_quantifier,antecedent,instantiation
shape: irule cannot instantiate universally-quantified variables appearing only in antecedents; use metis_tac or Q.INST/drule instead
pattern: When a lemma has !vt. A vt ==> B where vt appears only in antecedents not conclusion B, irule matching B against the goal creates a universal subgoal A vt' that simp cannot close even when A c is a specific assumption. Use metis_tac[lemma] instead, or specialize with Q.INST before irule, or use drule to match antecedents directly.
works_when: Applying lemmas with universally-quantified variables that appear only in antecedents
evidence:
- episode:E0128
- tool_output:TO_type_system_rewrite-20260516T153850Z_m17255_t001

## L0607 scope='global' tags=audit,cheat,grep,verification
shape: Always run fresh grep audits before claiming completion
pattern: Never trust stale observations about cheat counts. Before proposing task completion: (1) grep 'cheat' in all in-scope .sml files, (2) grep 'suspend' in same, (3) grep '\[oracles:' in .Theory.txt files, (4) holbuild full target, (5) check for 'CHEAT' in holbuild output warnings. The semantics/prop/ directory has ~80+ cheats across 3 in-scope files (vyperTypeBuiltinsScript.sml, vyperTypeStmtSoundnessScript.sml, vyperTypeCallSoundnessScript.sml).
works_when: Auditing for task completeness before end_session proposal
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m17769_t002

## L0735 scope='global' tags=dimword,w2n_lt,irule
shape: Proving w2n (word_expr) < 2 ** 256 using w2n_lt
pattern: When proving w2n (w:256 word) < 2**256, irule w2n_lt fails because 2**256 is a computed numeral. Fix: state the lemma as w2n w < dimword(:256) and prove via irule w2n_lt. If the consumer needs 2**256, add dimword_def + EVAL dimindex(:256) at the call site.
works_when: Word size bounds where 2**n would be computed to a large numeral
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m20266_t001

## L0736 scope='global' tags=gvs,conjunction,conj_tac
shape: Goal is non-conjunctive after gvs[] that was originally a conjunction
pattern: After gvs[] with assumptions, gvs may resolve one conjunct from a conjunction in the goal, leaving only the other. Always add a FAIL_TAC probe after gvs to inspect the actual goal before using conj_tac or other structural tactics. If gvs already split the conjunction, proceed directly.
works_when: gvs[] in proofs that simplify goal conjunctions using assumptions
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m20217_t002

## L0737 scope='global' tags=Num_int_lt,integer,monotonicity
shape: Proving Num i < bound from 0 <= i and i < j and Num j < bound
pattern: Use vyperArithTheory.Num_int_lt: 0 <= a /\ a < b ==> Num a < Num b. Combined with int_shift_right_nonneg_bounds (gives 0<= and <=), this bridges integer ordering to nat ordering for non-negative integers.
works_when: Converting integer < to Num < for non-negative integers, especially in within_int_bound unsigned range proofs
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m20238_t001

## L0752 scope='global' tags=file_corruption,write_file,restore,git
shape: Accidental write_file truncation of large HOL4 source files
pattern: When write_file overwrites a HOL4 source file, it destroys ALL content. Recovery: use git show HEAD:path to get committed version, then write_file to restore. If uncommitted changes existed, check git stash or reflog. ALWAYS read current file state before write_file. Prefer replace_text/edit_lines for targeted edits to avoid accidental truncation.
works_when: HOL4 source file accidentally truncated or overwritten
evidence:
- source:semantics/prop/vyperTypeBuiltinsScript.sml

## L0758 scope='global' tags=git_stash,lost_edits,file_recovery
shape: When dossier says proved but source has cheat, check git stash for lost edits
pattern: If a dossier episode claims a component was proved (result='proved') but the current source still has cheat for that theorem, the edits may be in a git stash. Run: git stash list, git show stash@{N}:path/to/file | wc -l (compare line count). If the stash has a larger file with the proved version, use git show stash@{N}:path > content then write_file to restore. This recovers entire proved file contents in one step instead of reproving from scratch.
works_when: Previous session proved theorems but edits were lost due to context clear, failed commit, accidental overwrite, or git reset.
evidence:
- episode:E0151
- tool_output:TO_type_system_rewrite-20260516T153850Z_m20876_t001

## L0864 scope='global' tags=
shape: Theorem with !msg. f <> INR(TypeError msg) conclusion: avoid fs[] and gvs[] entirely; use simp[] + mp_tac or REWRITE_RULE
pattern: When proving theorems of the form !msg. f x <> INR(TypeError msg), NEVER use fs[] or gvs[]. Three failure modes: (1) fs[] can rewrite the disequation using type-classifier equalities derived from assumptions, producing F; (2) gvs[] eliminates the !msg variable, producing an unsolvable concrete disequation; (3) both fire catch-all [simp] rules like is_int_type _ = F on free type variables. Safe alternatives: simp[] (changes conclusion only), qpat_x_assum mp_tac >> simp[] >> strip_tac, or pure REWRITE_RULE.
works_when: Any no-TypeError theorem with universally-quantified msg in a disequation conclusion, especially with type classifier assumptions on free variables
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m23247_t001
- tool_output:TO_type_system_rewrite-20260516T153850Z_m23345_t002
- tool_output:TO_type_system_rewrite-20260516T153850Z_m23369_t002

## L0892 scope='global' tags=definition_mismatch,constructor_names,Cases_on,unprovable
shape: msg ≠ string_literal goal after Cases_on + gvs with definition expansion
pattern: CRITICAL: Before any case-split proof over an algebraic type, grep both the Datatype definition AND any well_typed_* definition for constructor name mismatches. If well_typed_foo_def uses constructor X but the Datatype has Y, Cases_on will create impossible branches. Symptoms: msg ≠ 'string' goals from catch-all | _ => INR(TypeError 'string') branches. Fix: update well_typed_* definition to use correct Datatype constructor names.
works_when: Any proof that Cases_on's a type and then gvs's with a *rules* or *def* theorem that may use stale constructor names
evidence:
- source:semantics/prop/vyperTypeSystemScript.sml:93-96
- source:syntax/vyperASTScript.sml:60-63
- tool_output:TO_type_system_rewrite-20260516T153850Z_m24333_t001

## L0917 scope='global' tags=Unicode,parentheses,parse_error,theorem_statement
shape: HOL4 theorem statement parse errors: check for missing closing parentheses in ∀-wrapped conjuncts
pattern: When writing a theorem with a conjunctive conclusion where each conjunct has a ∀msg. ... wrapper, ensure EACH conjunct has its own closing paren: (!msg. A msg) ∧ (!msg. B msg). Missing the closing ) on the last conjunct gives a cryptic 'Don't expect to find a <end of input>' parse error. Also, Unicode ∨ is valid HOL4 syntax in backtick quotations (existing code uses it widely), but use \/ if concerned about API corruption.
works_when: Writing conjunctive theorem statements with universal quantifiers in each conjunct
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m25106_t001

## L0936 scope='global' tags=C4,builtin,no-TypeError,disjunction,strip_tac
shape: C4 builtin no-TypeError helper style
pattern: For builtin no-TypeError helpers with conclusion `!msg. evaluate_builtin ... <> INR (TypeError msg)`, avoid disjunctive premises and avoid stripping the `!msg` disequation into contradiction. State one helper per concrete post-`gvs[well_typed_builtin_app_def]` branch; prove direct helpers by `strip_tac >> gen_tac` followed by targeted theorem/definition expansion, not `rpt strip_tac` or generic disjunction destructuring.
works_when: C4/vyperTypeBuiltins dispatcher cases after `gvs[well_typed_builtin_app_def]` split bytes vs string/other alternatives into separate subgoals.
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m25561_t001
- tool_output:TO_type_system_rewrite-20260516T153850Z_m25409_t001
- tool_output:TO_type_system_rewrite-20260516T153850Z_m25602_t002

## L0937 scope='global' tags=edit,replace_text,Unicode,HOL4
shape: HOL4 SML edits with Unicode/backslash syntax
pattern: Prefer exact `replace_text` for surgical HOL4 proof-body edits. Avoid `edit_lines` on SML containing Unicode math or backslash-heavy ASCII logical syntax, because past tool calls corrupted such content. If exact replacement fails once, read the exact file fragment and use the smallest possible replacement; check `git diff` and source after writing.
works_when: Editing existing HOL4 SML proofs/theorems in this task through API tools.
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m21884_t001
- tool_output:TO_type_system_rewrite-20260516T153850Z_m20368_t001
- tool_output:TO_type_system_rewrite-20260516T153850Z_m23985_t001

## L0938 scope='global' tags=statement,assignment,assignable_context,materialise
shape: Statement assignment/call-site assignment context bridges
pattern: For statement assignment branches, avoid reproving a generic assign_target INL bridge unless a consumer demands it. Use focused bridges at call sites: `assign_target_no_type_error`/`assign_target_update_no_type_error` for INR Error, `assign_target_no_return` to eliminate ReturnException, `materialise_typed_non_none_no_type_error` after unfolding `expr_result_typed_def`, and static/TopLevelVar context projection lemmas for assignable context. Keep runtime_consistent/env_consistent definitions opaque; derive projection witnesses with targeted drule rather than huge fs expansions.
works_when: C2/C5 statement assignment soundness after assignment preservation side conditions are required.
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m17380_t001
- tool_output:TO_type_system_rewrite-20260516T153850Z_m17452_t001
- episode:E0129

## L0942 scope='global' tags=plan-gate,oracle-review,tool_limit,handoff
shape: query_plan says beginable but begin_component blocks on pending review
pattern: When query_plan and begin_component disagree, treat begin_component as the authoritative edit/build gate. If begin_component reports a pending closed-episode review, do not edit even if query_plan lists a beginable component; resolve the pending review or report a harness/tool_limit blocker.
works_when: Applies to structured PLAN gate inconsistencies after close_episode, especially when plan_oracle review calls fail but query_plan has already advanced the frontier.
evidence:
- tool_output:TO_type_system_rewrite-20260518T204229Z_m25827_t003
- tool_output:TO_type_system_rewrite-20260518T204229Z_m25801_t001

## L1289 scope='C2.1.1' tags=Resume,well_typed_expr,type_place_expr,place_projection,adapter
shape: Expression Resume goal has joint ordinary/place projections for a constructor.
pattern: Split the expression Resume conclusion into ordinary and place projections before consuming constructor typing. In ordinary branches, strip/use only `well_typed_expr`; in place branches, strip/use `type_place_expr`. For place-capable constructors, use adapter/helper lemmas whose conclusions match the branch, rather than carrying monadic tail unfolding in the Resume.
works_when: Applies to `eval_all_type_sound_mutual` expression Resume branches after the ordinary/place strengthened invariant, especially Subscript and TopLevelName-like place cases.
evidence:
- episode:E0663
- episode:E0664
- episode:E0695
- tool_output:TO_type_system_rewrite-20260522T073012Z_m39727_t001

## L1290 scope='C2.1.1' tags=Resume,adapter,guarded-IH,monadic-tail,proof-interface
shape: Large expression Resume branch times out or leaves outer goals after applying a helper/adapter.
pattern: Treat this as a helper-interface problem. Factor a small branch adapter that consumes the exact static split, guarded IHs, and evaluator-tail equality, then in the Resume project the needed IH and apply the adapter with explicit specialization if variables appear only in antecedents. Avoid broad `simp[]`/`metis_tac[]` and long inline tail rewrites.
works_when: Applies in large mutual evaluator Resume proofs with guarded IHs and monadic tails, particularly Expr_Subscript ordinary/place adapters.
evidence:
- episode:E0688
- episode:E0696
- episode:E0699
- tool_output:TO_type_system_rewrite-20260522T073012Z_m39950_t001

## L1291 scope='C2.3' tags=Expr_Pop,PopOp,assignable_type,definition_repair,boundary-lemma
shape: Pop typing/static interface must supply dynamic-array assignability for assignment soundness.
pattern: Do not derive Pop assignment side conditions from runtime `evaluate_type` facts. The source Pop typing rule should expose a dynamic target and `assignable_type env.type_defs (ArrayT elem_ty (Dynamic n))`; use extraction lemmas and the Pop result boundary rather than unfolding `assignable_type_def` or re-proving fixed-array counterexamples.
works_when: Applies to Expr_Pop statement soundness and consumers of `PopOp` assignment soundness in the fresh stack.
evidence:
- episode:E0712
- episode:E0713
- episode:E0718
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40415_t001

## L1292 scope='C2.3.6' tags=Expr_Pop,Resume,assign_target_pop_success_some_typed,assignable_type,boundary-lemma
shape: Expr_Pop Resume needs assignment-success result typing after `assign_target ... PopOp` returns `INL popped`.
pattern: Keep Expr_Pop at the statement-consumer level: use `well_typed_expr_Pop_dynamic_target_assignable` for dynamic target + assignability, build `target_runtime_typed`, derive `evaluate_type env.type_defs elem_ty = SOME elem_tv`, and use `assign_target_pop_success_some_typed` to rewrite the successful `lift_option_type popped` branch. Do not unfold `assign_target_def` or `assignable_type_def` in this Resume.
works_when: Applies inside `Resume eval_all_type_sound_mutual[Expr_Pop]` after the base-target IH has produced `location_runtime_typed` and `target_path_type` facts and the proof has split `assign_target` result.
evidence:
- episode:E0727
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40688_t002
- plan:C2.3.6

## L1293 scope='C2.3.6' tags=HOL4,THEN1,conj_tac,Cases_on,precedence,Expr_Pop
shape: A Resume proof uses `conj_tac >- (...) >> ...` or `Cases_on x >> simp[] >- ... >> ...` and holbuild shows the whole original conjunction or `GEN_TAC not a forall`.
pattern: In suspended expression Resume proofs, parenthesize branch tacticals aggressively: use `(conj_tac >- ordinary_tac >> place_tac)` and `(Cases_on `tm` >- error_tac >> success_tac)` rather than relying on `>>`/`>-` precedence. Unparenthesized forms can route later tactics to the wrong subgoal and make semantic goals look unsolved even when the intended branch progressed.
works_when: Applies when a proof has nested case splits inside the ordinary half of a joint ordinary/place expression soundness goal, especially around `Expr_Pop` and assignment-result splits.
evidence:
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40711_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40721_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40754_t001

## L1294 scope='C2.3.6' tags=HOL4,suspend,Resume,Expr_Pop,branch-structure,THEN1
shape: A statement Resume has a nested assignment-result split and inline tactics keep leaking or producing unreadable goals.
pattern: Factor the nested split with `suspend` labels and prove each branch as a separate `Resume` block. For Expr_Pop, the main Resume suspends `Expr_Pop_assign_inl` and `Expr_Pop_assign_inr`; the INL Resume proves runtime consistency and `?v. popped = SOME v /\ value_has_type elem_tv v` via `assign_target_pop_success_some_typed`, while the INR Resume uses `assign_target_preserves_runtime_consistent_result` and `assign_target_no_type_error`. Do not add an early `Finalise`; leave finalisation at the existing end of the mutual proof after all labels are resumed.
works_when: Use when an existing suspended mutual theorem already has many Resume blocks and a consumer proof needs two small post-case obligations with different boundary lemmas.
evidence:
- episode:E0729
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40813_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40810_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:7690-7760

## L1295 scope='global' tags=audit,source-authoritative,rebased-plan,holbuild
shape: PLAN leaf names a theorem, but DOSSIER has stale stuck subepisodes while current source may already have `Proof ... QED`.
pattern: Before editing a rebased leaf, grep/read the exact current-source theorem region and build the owning theory. If the named theorem and immediate corollaries have no `cheat` and the target builds, close the component with source+holbuild evidence instead of retrying stale tactic histories.
works_when: The task says current SML source is authoritative and the PLAN leaf statement is a current-source theorem name; especially useful after PLAN rebase/component identity drift.
evidence:
- episode:E0732
- episode:E0733
- episode:E0734
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40848_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40856_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40864_t001

## L1296 scope='C4.2' tags=builtin,success-typing,boundary-helper,probe,not
shape: Generic builtin success theorem has many residual constructor goals after replacing final cheat with FAIL_TAC; first goal is `Not`/`UintT n` value_has_type for computed complement.
pattern: When a generic builtin success theorem stalls after no-TypeError helper work, do not try to close residuals by broad catch-all simplification. Use the FAIL_TAC probe to identify the first constructor/value shape, then add a focused local success-typing helper for that constructor and dispatch the generic theorem through helpers. No-TypeError helpers are not substitutes for success-typing helpers.
works_when: The evaluator is non-recursive and the residual goal exposes a concrete builtin constructor with value/type assumptions (e.g. `evaluate_builtin ... Not [IntV i] = INL v` and a `value_has_type` conclusion).
evidence:
- episode:E0736
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40891_t001
- source:semantics/prop/vyperTypeBuiltinsScript.sml:2366-2410

## L1297 scope='C4.2' tags=builtin,success-typing,constructor-dispatch,slice,LIST_REL_EL_EQN
shape: Generic builtin success residual for a 3-argument builtin has MAP/evaluate_type equality plus `LIST_REL value_has_type tvs vs`, and goal needs result value typing.
pattern: For 3-argument builtin success cases (e.g. Slice), derive stable argument facts via `LIST_REL_EL_EQN` or a length helper such as `list_el_decomp_3`; avoid nested tail destructs. Then call a small evaluator-boundary lemma (`evaluate_slice_BytesT_success_type` / `evaluate_slice_StringT_success_type`) that reasons at implementation level once.
works_when: The static typing branch fixes a concrete argument list shape like `[arg_ty; BaseT (UintT 256); BaseT (UintT 256)]`, and `LIST_REL value_has_type tvs vs` connects evaluated type_values to runtime values.
evidence:
- episode:E0737
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40977_t001
- source:semantics/prop/vyperTypeBuiltinsScript.sml:1491-1526

## L1298 scope='C4.2' tags=builtin,success-typing,concat,boundary-helper
shape: Concat success residual: all static args are bytes or all strings, `evaluate_builtin ... (Concat n) vs = INL v`, goal is bounded Dynamic bytes/string value.
pattern: Prove concat success through loop-boundary lemmas (`evaluate_concat_loop_bytes_success_type`, `evaluate_concat_loop_string_success_type`). In the dispatcher, use `LIST_REL_value_has_type_imp_combined` plus `list_rel_bytes_all_bytesv` / `list_rel_string_all_stringv`, unfold `evaluate_concat_def` only after establishing all runtime values have the expected constructor, then apply the loop success lemma.
works_when: The `well_typed_builtin_app` branch gives `EVERY (λt. ∃bd. t = BaseT (BytesT bd)) ts` or `EVERY (λt. ∃m. t = BaseT (StringT m)) ts` and `2 <= LENGTH ts`.
evidence:
- episode:E0737
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40971_t001
- source:semantics/prop/vyperTypeBuiltinsScript.sml:1253-1275
- source:semantics/prop/vyperTypeBuiltinsScript.sml:2505-2527

## L1299 scope='C4.2' tags=builtin,success-typing,MakeArray,boundary-helper,sparse_has_type,compatible_bound
shape: MakeArray success residual: `well_typed_builtin_app ty (MakeArray o' bd) ts`, MAP/evaluate_type and LIST_REL value typing, evaluator returns `INL v`, goal `value_has_type tv v`.
pattern: Factor MakeArray success into a local boundary helper instead of handling it in the generic dispatcher. Tuple/NONE case uses `evaluate_type_TupleT_cases` plus `values_have_types_LIST_REL`; Array/SOME case uses `evaluate_type_ArrayT_SOME`, combined LIST_REL over source types, `LIST_REL_every_same_type_EVERY_vht`, and then `sparse_has_type_enumerate` for fixed arrays or `all_have_type_EVERY` for dynamic arrays. For fixed arrays, prove the length bound explicitly from `compatible_bound (Fixed n) (LENGTH ts)` and `LIST_REL_LENGTH`; the naive `drule LIST_REL_LENGTH >> simp[compatible_bound_def]` left an implication unsolved.
works_when: Static typing branch is the fresh `well_typed_builtin_app` MakeArray rule (`NONE` gives `ty = TupleT ts`; `SOME elem_ty` gives `ty = ArrayT elem_ty bd`, compatible bound, and `EVERY ($= elem_ty) ts`).
evidence:
- tool_output:TO_type_system_rewrite-20260522T073012Z_m41022_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m41056_t001
- source:semantics/prop/vyperTypeBuiltinsScript.sml:1680-1728

## L1300 scope='C4.2' tags=builtin,success-typing,Slice,boundary-helper,dispatcher
shape: Generic Slice success residual under MAP/evaluate_type equality and LIST_REL value typing, goal bounded BytesV/StringV result.
pattern: For Slice, a direct generic TRY can fail silently when length facts are hard to derive. A robust approach is to prove concrete boundary helpers `slice_bytes_builtin_success_type` and `slice_string_builtin_success_type` whose statements mirror the exact evaluated-type list shape produced by `evaluate_type_def`, then dispatch the generic theorem with `metis_tac` on the helper. This reduced residuals past both bytes and string Slice cases.
works_when: The generic proof has already simplified `well_typed_builtin_app` and `evaluate_type_def`, so the first assumption is an exact 3-element `MAP SOME tvs` equality for bytes or string plus two Uint256 arguments.
evidence:
- tool_output:TO_type_system_rewrite-20260522T073012Z_m41014_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m41016_t001
- source:semantics/prop/vyperTypeBuiltinsScript.sml:1538-1583
- source:semantics/prop/vyperTypeBuiltinsScript.sml:2624-2628

## L1301 scope='C4.2' tags=builtin,success-typing,dispatcher,modular-arithmetic,metis-timeout
shape: Generic success residual for AddMod/MulMod/PowMod256 has concrete Uint256 result existential after helper exists.
pattern: For modular arithmetic builtin success residuals, prove a local helper with conclusion `value_has_type (BaseTV (UintT 256)) v`. In the generic dispatcher, avoid `metis_tac[helper,value_has_type_def]` directly because it can time out; instead assert `value_has_type (BaseTV (UintT 256)) v` by the helper and then simplify `value_has_type_def` to discharge the concrete existential.
works_when: The residual has `MAP SOME tvs = [SOME (BaseTV (UintT 256)); ...]`, `LIST_REL value_has_type tvs vs`, and `evaluate_builtin ... AddMod/MulMod/PowMod256 vs = INL v`.
evidence:
- tool_output:TO_type_system_rewrite-20260522T073012Z_m41115_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m41119_t001
- source:semantics/prop/vyperTypeBuiltinsScript.sml:1799-1843
- source:semantics/prop/vyperTypeBuiltinsScript.sml:2771-2782

## L1302 scope='C4.2' tags=builtin,success-typing,Bop,boundary-wrapper,get_tenv
shape: Generic success residual for `evaluate_builtin cx acc ty (Bop b) vs = INL v` with two evaluated argument types and LIST_REL values.
pattern: Wrap `well_typed_binop_success_type` in a builtin-facing helper whose statement uses `evaluate_builtin ... (Bop bop) vs` and `get_tenv cx` directly. After a small two-element list simplification, call `well_typed_binop_success_type` with `u = case type_to_int_bound ty of NONE => Unsigned 0 | SOME u => u`. This avoids brittle in-place qspec/qexists plumbing in the generic dispatcher.
works_when: The generic proof has simplified `well_typed_builtin_app` enough to expose `well_typed_binop ty b h h'`, `[evaluate_type (get_tenv cx) h; evaluate_type (get_tenv cx) h'] = MAP SOME tvs`, and `evaluate_builtin ... (Bop b) vs = INL v`.
evidence:
- tool_output:TO_type_system_rewrite-20260522T073012Z_m41125_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m41127_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m41129_t001
- source:semantics/prop/vyperTypeBuiltinsScript.sml:1127-1142

## L1303 scope='C4.2' tags=builtin,success-typing,BlockHash,BlobHash,retired-proof-pattern
shape: After Bop residuals, next generic success goal for BlockHash: `evaluate_builtin ... (BaseT (BytesT (Fixed 32))) BlockHash [IntV i] = INL v` and goal `∃bs. v = BytesV bs ∧ LENGTH bs = 32`.
pattern: For BlockHash/BlobHash success, mine retired `vyperBuiltinTypingScript.sml` before tactic search. BlockHash uses `evaluate_block_hash_def` plus a helper like `evaluate_block_hash_well_typed`; BlobHash uses `evaluate_blob_hash_def`. Both close the bytes32 typing goal with `LENGTH_word_to_bytes_be_32`.
works_when: The residual is a bytes32 result for BlockHash/BlobHash under Uint256-typed index and an `INL` evaluator equation.
evidence:
- tool_output:TO_type_system_rewrite-20260522T073012Z_m41129_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m41130_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m41131_t002
- source:semantics/prop/vyperBuiltinTypingScript.sml:1168-1180

## L1304 scope='C4.2' tags=builtin,success-typing,dispatcher,constructor-boundary,ECRecover,ECAdd,ECMul
shape: Generic builtin success residual exposes concrete builtin evaluator equation and a `value_has_type`/existential result goal.
pattern: For remaining non-recursive builtin success cases, prove a small evaluator-facing success helper whose conclusion is exactly `value_has_type expected_tv v` (or derive that conclusion before simplifying existential goals). BlockHash/BlobHash use bytes length helpers; Acc specializes `Acc_builtin_sound`; MethodId uses `LENGTH_TAKE` and `LENGTH_Keccak_256_w64`; ECRecover needs `evaluate_ecrecover_typed`; ECAdd/ECMul need `evaluate_ecadd_well_typed`/`evaluate_ecmul_well_typed` wrappers over bn254 result bounds. Dispatching by direct helper-to-`value_has_type_def` metis is less reliable than first deriving the `value_has_type` fact, then simplifying.
works_when: The generic theorem has already inverted `well_typed_builtin_app` and `evaluate_type_def` enough to expose a concrete `evaluate_builtin ... BuiltinName ... = INL v` assumption and the expected runtime type is syntactically known.
evidence:
- episode:E0739
- tool_output:TO_type_system_rewrite-20260522T073012Z_m41147_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m41172_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m41185_t001
- source:semantics/prop/vyperTypeBuiltinsScript.sml:1936-1957
- source:semantics/prop/vyperTypeBuiltinsScript.sml:2228-2420
- source:semantics/prop/vyperTypeBuiltinsScript.sml:2572-2620
- source:semantics/prop/vyperTypeBuiltinsScript.sml:3090-3106

## L1305 scope='C4' tags=return_def,name-shadowing,vyperState,qualified-theorem
shape: Goal/assumption involves Vyper state monad `return x st = (INL y, st')`, but simplification with unqualified `return_def` does not unfold it.
pattern: In `vyperTypeBuiltinsScript.sml`, prefer `vyperStateTheory.return_def` (and `vyperStateTheory.bind_def` when needed) for state-monad proofs. Imports added for builtin/bn254/vfmExecution can make unqualified `return_def` refer to the wrong theory or fail to rewrite; a local helper like `return_INL_value` should be proved with `simp[vyperStateTheory.return_def, pairTheory.PAIR_EQ, sumTheory.INL_11]`.
works_when: The term is the Vyper state monad `return` from `vyperState`, especially in theorems about `toplevel_array_length` or other state computations returning `(INL v, st')`.
evidence:
- tool_output:TO_type_system_rewrite-20260522T073012Z_m41220_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m41227_t001
- source:semantics/prop/vyperTypeBuiltinsScript.sml:3111-3115

## L1306 scope='C4.3' tags=Extract32,type-builtin,static-predicate,counterexample,no-TypeError
shape: No-TypeError theorem for `evaluate_type_builtin ... Extract32 (BaseT bt) [bytes; idx]` has no premise restricting `bt`.
pattern: If Extract32 no-TypeError leaves an unrestricted target base type, stop and repair the static predicate. `evaluate_extract32` only avoids TypeError for fixed bytes, uint, int, and address; unsupported bases such as BoolT are a concrete counterexample under the old `well_typed_type_builtin_args` clause.
works_when: Applies to C4.3/C4.4 type-builtin proofs where `well_typed_type_builtin_args Extract32` is used to justify runtime behavior. After repair, use/derive `extract32_result_base_ok bt` from the static predicate before simplifying `evaluate_extract32_def`.
evidence:
- episode:E0741
- tool_output:TO_type_system_rewrite-20260522T073012Z_m41314_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m41320_t001

## L1307 scope='C4.3' tags=Extract32,type-builtin,boundary-helper,no-TypeError
shape: Main theorem branch has `well_typed_type_builtin_args Extract32 ...` and `evaluate_type_builtin ... Extract32 ... <> INR (TypeError msg)`.
pattern: After the Extract32 static repair, derive/use `extract32_result_base_ok bt` from `well_typed_type_builtin_args_def` and apply `evaluate_extract32_supported_no_type_error` in consumers. Avoid unfolding `evaluate_extract32_def` in the main theorem; destruct typed byte/int arguments only inside the local helper.
works_when: Applies in C4.3/C4.4 consumers after C4.3.1-C4.3.3 are in source. Runtime errors remain allowed; the helper excludes only TypeError.
evidence:
- episode:E0744
- episode:E0745
- tool_output:TO_type_system_rewrite-20260522T073012Z_m41360_t001
- source:semantics/prop/vyperTypeBuiltinsScript.sml:evaluate_extract32_supported_no_type_error

## L1311 scope='C4.4' tags=ABI,type-builtin,success-typing,boundary-lemma,enc,vyper_abi_size_bound,length-bound
shape: After unfolding `evaluate_abi_encode` success and dynamic-bytes `value_has_type`, goal is `LENGTH (enc (vyper_to_abi_type tenv typ) av) <= n` with `vyper_to_abi tenv typ vin = SOME av` and `vyper_abi_size_bound tenv typ <= n`.
pattern: For C4.4 ABI encode branches, prove a lower-level length boundary before touching resumes. A wrapper theorem `evaluate_abi_encode tenv typ vin = INL out ∧ evaluate_type tenv typ = SOME tv ∧ value_has_type tv vin ∧ evaluate_type tenv (BaseT (BytesT (Dynamic n))) = SOME result_tv ∧ vyper_abi_size_bound tenv typ <= n ==> value_has_type result_tv out` reduces mechanically to the encoded-length lemma. The reusable missing lemma is `vyper_to_abi` success under Vyper typing implies `LENGTH (enc (vyper_to_abi_type tenv typ) av) <= vyper_abi_size_bound tenv typ`; prove it once (likely in `vyperTypeABIScript.sml`) and consume it in the wrapper/resumes.
works_when: Use for `well_typed_type_builtin_success_type[abi_encode]`, `[encode_tuple]`, and `[encode_tuple_nowrap]`. For dynamic bytes/string cases expect to need monotonicity of `ceil32`; for tuple/array/struct cases expect recursion through `vyper_abi_size_bound_list`/`vyper_abi_embedded_size`. Do not use `enc_valid` until the length premise is available.
evidence:
- tool_output:TO_type_system_rewrite-20260522T073012Z_m41466_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m41465_t001
- episode:E0752
- plan:C4.4

## L1312 scope='C4.4' tags=ABI,vyper_to_abi,contractABI.has_type,length-bound,helper-interface
shape: A Vyper-to-ABI typing bridge using `contractABI$has_type` leaves tuple/array goals such as `LENGTH avs < dimword(:256)` even after element typing is proved.
pattern: For C4.4, do not treat `vyper_to_abi_well_typed` as a pure element-typing theorem. `contractABI$has_type` includes `valid_length` for tuples/arrays, so any helper concluding `has_type (vyper_to_abi_type tenv typ) av` needs explicit length/bound facts from `evaluate_type`, `value_has_type`, and conversion length lemmas. If those bounds are not already in the statement, prove the direct encoded-length theorem instead of pushing `gvs` on the broad helper.
works_when: Applies when a helper has conclusion `has_type (vyper_to_abi_type tenv typ) av` or `has_types (vyper_to_abi_types tenv ts) avs` and holbuild leaves `LENGTH avs < dimword(:256)` subgoals. Split the helper or add side conditions; do not solve by resume-level plumbing.
evidence:
- tool_output:TO_type_system_rewrite-20260522T073012Z_m41492_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m41493_t001

## L1313 scope='C4.4' tags=ceil32,arithmetic,DIV_LE_MONOTONE,ABI
shape: Need monotonicity of ABI `ceil32`: `m <= n ==> ceil32 m <= ceil32 n`.
pattern: In `vyperTypeABI`, `ceil32_def` is not directly in scope as `ceil32_def`; use `contractABITheory.ceil32_def`. A simple proof shape is `rw[contractABITheory.ceil32_def] >> \`m + 31 <= n + 31\` by simp[] >> irule DIV_LE_MONOTONE >> simp[]`. `drule_all DIV_LE_MONOTONE` does not match the division goal reliably here.
works_when: Use for dynamic bytes/string length cases, where `value_has_type` gives `LENGTH bs <= n` and the goal compares `32 + ceil32 (LENGTH bs)` with `32 + ceil32 n`.
evidence:
- tool_output:TO_type_system_rewrite-20260522T073012Z_m41485_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m41487_t001
- source:semantics/prop/vyperTypeABIScript.sml:139-145

## L1314 scope='C4.4.1' tags=ABI,enc_tuple,length-bound,accumulator,MAP2,SUM
shape: Need an upper bound for `LENGTH (enc_tuple hl tl ts vs hds tls)` or `LENGTH (enc (Tuple ts) (ListV vs))` under `has_types ts vs`.
pattern: Hide `enc_tuple` accumulators behind a generic ABI length lemma before proving Vyper-specific ABI encode bounds. The desired accumulator theorem bounds length by existing head/tail accumulator lengths plus a `SUM (MAP2 ...)` per-element budget: dynamic elements contribute `32 + LENGTH (enc t v)`, static elements contribute `static_length t`. Tuple/dynamic-array/fixed-array wrappers should be the only lemmas consumed by Vyper proofs.
works_when: Use before C4.4.4 `vyper_to_abi_enc_length_bound`; prove by induction on `ts` with cases on `vs`, `has_types` eliminating mismatches, `enc_def` unfolded once in the cons case, `LENGTH_enc_number` for dynamic heads, and `enc_has_static_length` for static heads.
evidence:
- tool_output:TO_type_system_rewrite-20260522T073012Z_m41522_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m41526_t001
- plan:C4.4.1

## L1315 scope='C2' tags=C2,Subscript,Pop,Attribute,boundary-helper,compacted
shape: Subscript/Pop/Attribute statement-expression resumes require boundary helpers and immediate IH projections
pattern: For future C2 resume repair, avoid replaying old long tactical histories from LEARNINGS. Query the dossier episodes cited here for the specific region, then use boundary helpers that return the whole evaluator suffix and immediately project strengthened IHs. Common subpatterns: Subscript place branches need the place-expression projection rather than coercion to ordinary well_typed_expr; Pop assignment paths should factor Pop result typing below assign_target; Attribute should use a field-ALOOKUP boundary helper.
works_when: Returning to C2 statement/expression mutual soundness after C4/C5 prerequisites; use dossier evidence for exact old branch-specific tactics instead of keeping dozens of stale per-branch learning cards.
evidence:
- episode:E0637
- episode:E0708
- episode:E0723
- episode:E0726
- episode:E0710

## L1316 scope='C4.4.1' tags=ABI,enc_tuple,length-bound,MAP2,SUM,boundary-lemma
shape: Need generic upper bounds for ABI tuple/dynamic-array/fixed-array encodings before Vyper ABI length theorem
pattern: Prove an accumulator `enc_tuple` bound once, then expose only clean wrappers: tuple wrapper over `enc (Tuple ts) (ListV vs)`, dynamic-array wrapper over `enc (Array NONE t)`, and fixed-array wrapper over `enc (Array (SOME n) t)`. Use `Once contractABITheory.enc_def`; dynamic heads need `byteTheory.LENGTH_word_to_bytes`; static heads need `cj 1 contractABITheory.enc_has_static_length`; repeated element budgets are handled by a small `SUM (MAP2 ... REPLICATE ...) <= LENGTH vs * embedded` helper. Keep accumulator instantiations inside these generic lemmas only.
works_when: C4.4.4 or later proof needs to bound ABI encoding lengths from `has_types`/`have_type`/`has_type (Array ...)` without exposing `hl`, `tl`, `hds`, or `tls` to Vyper-specific consumers.
evidence:
- episode:E0754
- tool_output:TO_type_system_rewrite-20260522T073012Z_m41583_t001
- source:semantics/prop/vyperTypeABIScript.sml:154-266

## L1317 scope='C4.4' tags=ABI,has_type,valid_int_bound,UintT,IntT,counterexample,encoded-length
shape: A helper tries to prove `contractABI.has_type (vyper_to_abi_type tenv typ) av` from Vyper `evaluate_type` / `value_has_type`.
pattern: Do not use ABI `has_type` as the main invariant for fresh Vyper ABI encode length proofs. Vyper permits unaligned integer widths (`UintT 1`, `IntT 2`, etc.) while `contractABI.has_type` requires `valid_int_bound n`, including byte alignment. Prove direct encoded-length facts using `enc_def`/`LENGTH_enc_number` and no-type tuple/array length wrappers instead.
works_when: Applies to `default_to_abi`, `vyper_to_abi`, sparse static-array defaults, and any ABI encode helper whose consumer only needs `LENGTH (enc ...) <= ...`. If a goal asks for `n MOD 8 = 0` from `evaluate_type`, abandon the ABI-typing invariant and switch to direct length.
evidence:
- episode:E0755
- tool_output:TO_type_system_rewrite-20260522T073012Z_m41625_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m41626_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m41628_t001

## L1318 scope='C4.4.3' tags=ABI,enc_tuple,actual-length,no-has_type,static-premise
shape: Need an unconditional tuple encoder length bound without ABI typing assumptions.
pattern: Use raw actual encoded lengths for every static element: prove `enc_tuple_acc_length_bound_actual` by induction on `ts` and cases on `vs`, one-step `contractABI.enc_def`, `LENGTH_FLAT`, reverse/SUM rewrites, and split on `is_dynamic h'`. In the dynamic branch, specialize the IH to tail `t`, updated `tl + LENGTH (enc h' h)`, offset head `word_to_bytes ...::hds`, and tail `enc h' h::tls`; in the static branch specialize to `enc h' h::hds` and `[]::tls`. Select the universal IH with `qpat_x_assum`, not fragile `first_x_assum`.
works_when: Use before static-premise tuple corollaries; it assumes no `has_type` and does not mention `static_length`. Downstream lemmas must separately prove static elements encode within `static_length`.
evidence:
- episode:E0762
- tool_output:TO_type_system_rewrite-20260522T073012Z_m41674_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m41677_t001

## L1319 scope='C4.4.3' tags=ABI,enc_tuple,ZIP,REPLICATE,static-premise
shape: Need to instantiate a ZIP premise over `ZIP (REPLICATE (LENGTH vs) t, vs)`.
pattern: Use a local membership bridge: `MEM (t',v) (ZIP (REPLICATE (LENGTH vs) t,vs)) <=> t' = t /\ MEM v vs`, proved from `MEM_ZIP`, `EL_REPLICATE`, `EL_MEM`, and `MEM_EL`. This lets `simp[MEM_ZIP_REPLICATE_SAME]` reduce static-element premises for tuple/array wrapper instantiations.
works_when: Applies to array encoder wrappers that reduce to tuple encoding over replicated ABI element types; avoid ABI `has_type_def`.
evidence:
- episode:E0765
- tool_output:TO_type_system_rewrite-20260522T073012Z_m41713_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m41718_t001

## L1320 scope='C4.4.3' tags=ABI,dynamic-array,enc_def,word_to_bytes,length-prefix
shape: Dynamic ABI array length wrapper using tuple accumulator over `Array NONE`.
pattern: After `simp[Once contractABITheory.enc_def, byteTheory.LENGTH_word_to_bytes]`, instantiate the tuple accumulator with `hds = [word_to_bytes (n2w (LENGTH vs) : bytes32) T]` and `tls = []`; the prefix contributes exactly 32. Omitting this hds entry leaves an impossible bound that is short by 32.
works_when: Use for `enc (Array NONE t) (ListV vs)` bounds, including default dynamic arrays and Vyper same-array conversion branches.
evidence:
- episode:E0765
- tool_output:TO_type_system_rewrite-20260522T073012Z_m41714_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m41717_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m41718_t001

## L1321 scope='C4.4.3' tags=ABI,MAP2,static-premise,arithmetic,induction
shape: Replicated MAP2 embedded-size bound with both dynamic and static element premises.
pattern: Induct on `vs`; when specializing the IH for the tail, discharge the three-part antecedent explicitly (`MEM` premise, guarded static premise, embedded inequality) rather than relying on broad `metis_tac`. Then split on `is_dynamic t`; dynamic branch uses the `elem_bound` premise for `h`, static branch needs only the embedded static inequality because the sum term already uses `static_length t`.
works_when: Applies to `SUM (MAP2 (\t v. if is_dynamic t then 32 + LENGTH (enc t v) else static_length t) (REPLICATE (LENGTH vs) t) vs)` bounds.
evidence:
- episode:E0764
- tool_output:TO_type_system_rewrite-20260522T073012Z_m41703_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m41705_t001

## L1322 scope='C4.4.4' tags=ABI,default_to_abi,fixed-array,enc_tuple,boundary-lemma
shape: Fixed-array default branch after `enc_def`: `LENGTH (enc_tuple (head_lengths (REPLICATE n t) 0) 0 (REPLICATE n t) (REPLICATE n v) [] []) <= n * embedded`.
pattern: For default fixed arrays, prove/apply a helper with the unfolded `enc_tuple (REPLICATE n ...)` conclusion. It should reduce to `enc_fixed_array_same_length_bound_static_premise` with `vs = REPLICATE n v`, an element encoded-length bound, a guarded static encoded-length bound, and `vyper_to_abi_embedded_head_bound`/`vyper_to_abi_type_dynamic` for the embedded size. This is more robust than matching the subterm inside the large `evaluate_type_ind` goal.
works_when: The branch has `evaluate_type tenv typ = SOME tv` and an IH/assumption for `LENGTH (enc (vyper_to_abi_type tenv typ) (default_to_abi tv)) <= vyper_abi_size_bound tenv typ`. For static case use `vyper_to_abi_static_length_bound`; no ABI `has_type` required.
evidence:
- tool_output:TO_type_system_rewrite-20260522T073012Z_m41760_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m41785_t001
- source:semantics/prop/vyperTypeABIScript.sml:509-595

## L1324 scope='C4.4.4.2' tags=ABI,default_to_abi,tuple,LIST_REL,MAP2,length-bound
shape: Need tuple encoded-length bound from `LIST_REL` element-good premises for `(vyper_to_abi_types tenv ts, MAP default_to_abi tvs)`.
pattern: Split the tuple consumer into two proof obligations: a static ZIP premise discharged from LIST_REL element-good plus `vyper_to_abi_type_dynamic`, and a MAP2/SUM bound discharged by LIST_REL/list induction using each head `LENGTH (enc ...) <= vyper_abi_size_bound` and `vyper_to_abi_embedded_head_bound`. Then apply `enc_tuple_length_bound_static_premise` to obtain the public `enc (Tuple ...)` length conclusion. Keep `enc_tuple` accumulator parameters out of the theorem statement.
works_when: Active C4.4.4.2 or later C4.4.4.4 compatibility derivation, after C4.4.3 static-premise tuple wrappers and C4.4.4.1 Vyper bridge helpers are available. If `evaluate_types` or arbitrary `hl/tl/hds/tls` appears in this consumer theorem, the abstraction boundary is wrong.
evidence:
- tool_output:TO_type_system_rewrite-20260522T073012Z_m41879_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m41881_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m41882_t004
- episode:E0766

## L1325 scope='C4.4.4.2' tags=ABI,LIST_REL,SUM_MAP2,default_to_abi,proof-interface
shape: Tuple default ABI bound from LIST_REL element premises; anonymous lambda causes brittle IH selection in MAP2/SUM induction.
pattern: Before proving ZIP/SUM tuple consumers, name the repeated element premise as `default_to_abi_elem_bound_rel tenv typ tv` and prove a pointwise head lemma whose conclusion exactly matches the MAP2 head contribution bounded by `vyper_abi_embedded_size`. Then prove static ZIP and SUM_MAP2 consumers from the named relation, preserving the final public theorem statement with the original LIST_REL lambda.
works_when: Use in C4.4.4.2.1-.4 and C4.4.4.3 when default ABI element/list facts feed tuple encoding bounds. Especially useful after repeated failures specializing IHs over anonymous LIST_REL lambdas.
evidence:
- episode:E0772
- tool_output:TO_type_system_rewrite-20260522T073012Z_m41942_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m41947_t001

## L1326 scope='C4.4.4.2' tags=ABI,LIST_REL,SUM_MAP2,induction,static_length
shape: SUM_MAP2 tuple bound cons case after LIST_REL split: tail SUM bound plus head dynamic/static contribution.
pattern: In the tuple SUM_MAP2 helper, a short robust proof is: induct on `ts`, split `tvs`, simplify `vyper_to_abi_type_def` and `vyper_abi_size_bound_def`, use the IH on the LIST_REL tail, then use `drule_all (cj 1 vyper_to_abi_type_dynamic)` and split on `vyper_is_dynamic tenv head`. Dynamic branch closes by arithmetic from the encoded-length head bound; static branch first applies `vyper_to_abi_static_length_bound`, then arithmetic. Do not rely on auto-generated `h/h'` names to instantiate a named relation.
works_when: Use when proving a MAP2/SUM bound over `(vyper_to_abi_types tenv ts, MAP default_to_abi tvs)` from the standard element LIST_REL premise. Assumes head conjuncts include `evaluate_type`, encoded-length bound, and static encoded-length implication.
evidence:
- episode:E0775
- source:semantics/prop/vyperTypeABIScript.sml:592-619
- tool_output:TO_type_system_rewrite-20260522T073012Z_m41993_t001

## L1327 scope='C4.4.4.3' tags=ABI,LIST_REL,evaluate_type_ind,enc_tuple,boundary
shape: Default ABI length proof where evaluate_types cons branch exposes `enc_tuple` accumulator/head_lengths goals.
pattern: Do not prove ABI tuple length/SUM/static facts in the `evaluate_types` recursive invariant. Prove a semantic suffix invariant `?dtvs. tvs = REVERSE acc ++ dtvs /\ LIST_REL (default_to_abi_elem_bound_rel tenv) ts dtvs`, then derive tuple length/SUM/static facts in a separate corollary from C4.4.4.2 tuple boundary lemmas.
works_when: Applies when evaluator recursion is over `evaluate_types` and tuple encoding goals appear only because a consumer theorem included ABI encoding facts in the recursive invariant.
evidence:
- episode:E0777
- tool_output:TO_type_system_rewrite-20260522T073012Z_m42061_t001

## L1328 scope='C4.4.4.3' tags=ABI,LIST_REL,ZIP,struct,MAP_ZIP,boundary
shape: Struct default ABI case produces `MAP (default_to_abi o SND) (ZIP (MAP FST args,tvs))` but tuple boundary lemmas expect `MAP default_to_abi tvs`.
pattern: Package the struct ZIP shape with a small lemma: if `LENGTH names = LENGTH tvs`, then `MAP (default_to_abi o SND) (ZIP (names,tvs)) = MAP default_to_abi tvs`. In struct cases, derive the length from `LIST_REL_LENGTH` and `LENGTH_MAP`, rewrite with this lemma, then apply the ordinary tuple LIST_REL boundary lemmas.
works_when: Applies to ABI/default struct proofs where evaluated field type-values `tvs` are zipped with field names only for StructV/StructTV packaging, but tuple encoders operate on the value suffix list.
evidence:
- source:semantics/prop/vyperTypeABIScript.sml:673-679
- tool_output:TO_type_system_rewrite-20260522T073012Z_m42130_t001
- episode:E0778

## L1329 scope='C4.4.4.3' tags=ABI,LIST_REL,boundary,irule,qspecl_then
shape: Have `LIST_REL (default_to_abi_elem_bound_rel tenv) ts tvs`, need tuple boundary lemmas stated with expanded lambda relation or simplified `enc_tuple` goal.
pattern: Use `LIST_REL_mono` with witness `default_to_abi_elem_bound_rel tenv` plus `simp[default_to_abi_elem_bound_rel_def]` to derive the expanded lambda LIST_REL. For tuple helper conclusions that do not match after `enc (Tuple ...)` simplifies to `enc_tuple`, either use the local `default_to_abi_enc_tuple_bound_from_LIST_REL` wrapper or explicitly specialize the boundary theorem with `qspecl_then [`tenv`,`ts`,`tvs`] mp_tac ... >> simp[]`; avoid manual theorem plumbing.
works_when: Applies to default ABI corollaries after the semantic evaluator invariant has produced only `LIST_REL (default_to_abi_elem_bound_rel tenv)`.
evidence:
- episode:E0779
- source:semantics/prop/vyperTypeABIScript.sml:832-847
- tool_output:TO_type_system_rewrite-20260522T073012Z_m42159_t001

## L1330 scope='C4.4.5' tags=ABI,ceil32,enc,dynamic-bytes,arithmetic
shape: Goal after unfolding `enc String (BytesV bs)` or `enc (Bytes NONE) (BytesV bs)`: `len + 32 + (ceil32 len - len) <= ceil32 n + 32`.
pattern: Do not expect `decide_tac` alone to prove dynamic bytes/string encoded-length bounds. First derive `ceil32 len <= ceil32 n` using `ceil32_mono` from the Vyper length assumption, and derive `len <= ceil32 len` by simp (`le_ceil32`), then `decide_tac` closes the subtraction arithmetic.
works_when: Applies when Vyper `value_has_type` gives `STRLEN s <= n` or `LENGTH bs <= n`, and the ABI bound is `ceil32 n + 32`.
evidence:
- tool_output:TO_type_system_rewrite-20260522T073012Z_m42219_t001
- source:semantics/prop/vyperTypeABIScript.sml:873-893

## L1331 scope='C4.4.5' tags=ABI,sparse,boundary-relation,length-bound
shape: Sparse ABI conversion proof needs bounds for both converted values and default ABI values.
pattern: When a relation must feed sparse-array encoding, keep the per-ABI-value bound relation independent of source conversion and source `value_has_type`; defaults inserted for missing sparse entries have no `vyper_to_abi ... = SOME av` premise but still satisfy the same encoded-length interface via default-bound lemmas.
works_when: Applies to C4.4.5-style length-bound proofs where `vyper_to_abi_sparse` appends either an explicitly converted `av` or `default_to_abi tv`. Use a separate strengthened theorem to connect successful conversions to the relation.
evidence:
- tool_output:TO_type_system_rewrite-20260522T073012Z_m42259_t001
- episode:E0782
- source:semantics/prop/vyperTypeABIScript.sml:926-944

## L1332 scope='C4.4.5' tags=ABI,sparse,induction,IH
shape: Recursive sparse branch decreases `n` but keeps the same sparse map.
pattern: Do not use `sparse_has_type tv n sparse` as the strengthened sparse IH premise for `vyper_to_abi_sparse`; the `SUC n` recursive call reuses the same sparse map, which may contain key `n`. Use a length-independent predicate `sparse_values_have_type tv sparse = !k v. MEM (k,v) sparse ==> value_has_type tv v`.
works_when: Applies to proofs by `vyper_to_abi_ind` over `vyper_to_abi_sparse (SUC n) sparse`, especially when using `ALOOKUP sparse n`.
evidence:
- tool_output:TO_type_system_rewrite-20260522T073012Z_m42259_t001
- source:semantics/vyperABIScript.sml:509-519
- source:semantics/prop/vyperTypeABIScript.sml:941-944

## L1333 scope='C4.4.5' tags=ABI,array,boundary-lemma,irule,static-premise
shape: After `irule enc_dyn_array_same_length_bound_static_premise` or `irule enc_fixed_array_same_length_bound_static_premise`, the goal is a conjunction containing an existential element-bound subgoal plus a separate static-element premise.
pattern: Do not immediately `qexists` after applying the same-array static-premise lemmas. First split the top-level conjunctions: prove the length/element-bound conjunct by choosing `vyper_abi_size_bound tenv typ` and using `abi_av_bound_rel_def` plus `vyper_to_abi_embedded_head_bound`; prove the static premise separately by `EVERY_MEM` and `abi_av_bound_rel_static_premise`.
works_when: Applies when the context has `evaluate_type tenv typ = SOME tv` and `EVERY (abi_av_bound_rel tenv typ tv) avs`, and the goal is a dynamic/fixed same-type ABI array length bound.
evidence:
- episode:E0783
- tool_output:TO_type_system_rewrite-20260522T073012Z_m42280_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m42283_t001
- source:semantics/prop/vyperTypeABIScript.sml:1008-1046

## L1334 scope='C4.4.5' tags=ABI,sparse,ALOOKUP,induction
shape: Need `value_has_type tv v` from `sparse_values_have_type tv sparse` and `ALOOKUP sparse k = SOME v`.
pattern: If `ALOOKUP_MEM` is not available in the current theory namespace, prove the projection directly by induction on the sparse alist: split the head pair, simplify `sparse_values_have_type_def`, case-split `head_key = k`, and use the IH on the tail branch with the tail value predicate reconstructed from the head predicate.
works_when: Applies to local sparse projection facts in `vyperTypeABIScript.sml` without adding new imports or sortedness/key-bound premises.
evidence:
- episode:E0784
- tool_output:TO_type_system_rewrite-20260522T073012Z_m42309_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m42318_t001
- source:semantics/prop/vyperTypeABIScript.sml:1060-1070

## L1335 scope='C4.4.5.4' tags=ABI,dynamic-array,arithmetic,boundary-lemma
shape: Dynamic array Vyper-to-ABI branch after unfolding `enc (Array NONE ...)` has an implication `LENGTH enc_tuple ... <= emb * LENGTH vs + 32 ==> ... <= emb * n + 32`.
pattern: For dynamic array evaluated-VHT helper proofs, keep the array encoding boundary in `abi_avs_dyn_array_bound`, then after `simp[Once contractABITheory.enc_def, vyper_abi_size_bound_def]` abbreviate the embedded element size (`emb`) and prove `emb * LENGTH vs <= emb * n` from `LENGTH vs <= n` using `LESS_MONO_MULT` and `MULT_COMM`; then arithmetic is straightforward. Do not leave repeated conditional embedded-size expressions for `decide_tac`.
works_when: Applies when `evaluate_type tenv (ArrayT typ (Dynamic n)) = SOME tv`, `value_has_type tv (ArrayV (DynArrayV vs))`, and the same-array IH gives `EVERY ... avs` plus `LENGTH avs = LENGTH vs`.
evidence:
- tool_output:TO_type_system_rewrite-20260522T073012Z_m42381_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m42398_t001
- source:semantics/prop/vyperTypeABIScript.sml:1082-1108

## L1336 scope='C4.4.5.4' tags=ABI,tuple,struct,drule_all,boundary-lemma
shape: Tuple/struct branch has an induction hypothesis `!tvs. LIST_REL ... ts tvs /\ values_have_types tvs vs ==> abi_av_list_bound_rel ... tvs` and a goal about raw `enc_tuple ... <= vyper_abi_size_bound`.
pattern: Introduce a helper that unfolds `evaluate_type`/`value_has_type` just enough to recover the concrete `tvs`, proves `LIST_REL` via `evaluate_types_LIST_REL`, applies the all-`tvs` IH, and then uses `abi_av_list_tuple_bound_enc_tuple`. In consumers, prefer `drule_all helper` over direct `irule` because the helper's premise is a universally quantified IH plus evaluated/VHT assumptions.
works_when: Applies to `TupleT ts` and likely to `StructT id` after translating `struct_has_type` to `values_have_types (MAP SND ...) (MAP SND fields)`.
evidence:
- tool_output:TO_type_system_rewrite-20260522T073012Z_m42348_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m42356_t001
- source:semantics/prop/vyperTypeABIScript.sml:1020-1041

## L1337 scope='C4.4.5.5' tags=ABI,compatibility-corollary,drule_all,fixed-array,sparse
shape: Goal is exactly the fixed-array ABI length bound with `EVERY (abi_av_bound_rel ...) avs` and `LENGTH avs = n`; `drule_all abi_avs_fixed_array_bound` raises a HOL_ERR assertion.
pattern: For the exported sparse conjunct, prefer goal-driven `irule abi_avs_fixed_array_bound >> simp[]` or explicit `qspecl_then` specialization over `drule_all`. The lemma conclusion matches the goal; `LENGTH avs = n` should discharge the lemma's `LENGTH avs <= n` premise by simplification.
works_when: Applies in C4.4.5.5 after deriving `sparse_values_have_type` from `sparse_has_type` and applying conjunct 4 of `vyper_to_abi_bound_rel_strong`, so the context contains `evaluate_type`, `EVERY abi_av_bound_rel`, and `LENGTH avs = n`.
evidence:
- tool_output:TO_type_system_rewrite-20260522T073012Z_m42443_t001
- episode:E0787

## L1338 scope='C4.4.6' tags=ABI,builtin,irule,existential-witnesses,length-bound
shape: Goal `value_has_type result_tv v` from `evaluate_abi_encode ... = INL v` and size/type/value premises via `evaluate_abi_encode_success_type_bound`.
pattern: When using `evaluate_abi_encode_success_type_bound` as a backward rule, `irule` matches only the result `value_has_type result_tv v` and leaves existential witnesses for `n`, `tenv`, `tv`, `typ`, and `vin`. Immediately supply them with `qexistsl` from the live builtin branch, then `simp[]` discharges the premises.
works_when: Applies in `well_typed_type_builtin_success_type` ABI encode resumes after deriving the appropriate `vyper_abi_size_bound tenv typ <= n`, `evaluate_type tenv typ = SOME tv`, `value_has_type tv vin`, and `evaluate_abi_encode tenv typ vin = INL v` facts.
evidence:
- tool_output:TO_type_system_rewrite-20260522T073012Z_m42473_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m42477_t001
- source:semantics/prop/vyperTypeBuiltinsScript.sml:3358-3364

## L1339 scope='C4.4.6' tags=ABI,tuple,evaluate_type,type_slot_size,boundary-helper
shape: Need `evaluate_type tenv (TupleT ts) = SOME (TupleTV tvs)` from `MAP (evaluate_type tenv) ts = MAP SOME tvs`.
pattern: One-step tuple `evaluate_type` reconstruction is not just `OPT_MMAP`: after recovering the element type values it must also prove the tuple `type_slot_size` bound. Factor this as a local helper or derive the slot-size side condition explicitly before using the tuple ABI encode success helper.
works_when: Applies to `encode_tuple`/`encode_tuple_nowrap` builtin resumes where `type_builtin_result_ok` gives only an ABI encoded byte-size bound and the branch context gives `MAP evaluate_type = MAP SOME tvs`.
evidence:
- tool_output:TO_type_system_rewrite-20260522T073012Z_m42491_t001
- source:semantics/prop/vyperTypeBuiltinsScript.sml:3366-3378

## L1340 scope='C2.4.0' tags=exception,namespace,type-annotation,vyperState,statement-soundness
shape: HOL type error unifying `vfmExecution$exception` with `vyperState$exception` at a sum annotation like `(INR exn : unit + exception)`.
pattern: In `vyperTypeStmtSoundnessScript.sml`, explicit evaluator-result sum annotations must qualify the exception type as `vyperState$exception` (e.g. `unit + vyperState$exception` or `value + vyperState$exception`). Unqualified `exception` can resolve to another imported theory's exception type before tactics run.
works_when: Use for local helper theorem statements and quoted proof patterns that feed `return_exception_typed`, `stmt_error_ok`, `no_type_error_result`, or evaluator result cases in statement soundness.
evidence:
- tool_output:TO_type_system_rewrite-20260522T073012Z_m42539_t004
- tool_output:TO_type_system_rewrite-20260522T073012Z_m42540_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:48-55

## L1342 scope='C2.4.0' tags=body,namespace,type-annotation,eval_stmts,type_stmts,eval_for,statement-soundness
shape: HOL type error where `eval_stmts`, `type_stmts`, or `eval_for` expects a `stmt list` but bare `body` is inferred/resolved as a word64 function; or proof mismatch after renaming.
pattern: In `vyperTypeStmtSoundnessScript.sml` statement/for-cons helper prefixes, avoid the bare theorem variable name `body` for statement-list evaluator bodies. Rename user-controlled binders to `body_stmts` and higher-order computation bodies to `body_fun`; update theorem statements, proof quotations, `Cases_on`, `qmatch_*`, `qspecl_then`, and `qexists_tac` witnesses consistently. If the live goal already contains HOL-generated `body'`, use `body'` in local proof text rather than forcing `body_stmts`. A mere `(body : stmt list)` annotation may not override the imported/resolved `body` identifier.
works_when: Applies to source elaboration/name-resolution cleanup around evaluator bodies in C2.4.0-style statement-soundness prefix/helpers, especially before semantic resume obligations. Does not justify broad semantic changes once the theory builds.
evidence:
- tool_output:TO_type_system_rewrite-20260522T073012Z_m42558_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m42647_t001
- episode:E0791
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml

## L1343 scope='C2.4.1' tags=Expr_Builtin,Len,well_typed_builtin_app,eval_exprs,boundary-lemma
shape: Suspended `Expr_Builtin` branch of `eval_all_type_sound_mutual` with generated IHs split into `bt <> Len`/`eval_exprs` and `bt = Len`/`eval_expr (HD es)`.
pattern: For the fresh statement-soundness `Expr_Builtin` resume, exploit the induction-generated split instead of re-case-splitting blindly: non-Len branch should consume the `eval_exprs` IH and `well_typed_builtin_app_no_type_error`/`well_typed_builtin_app_success_type`; Len branch should consume the `eval_expr (HD es)` IH and `Len_builtin_sound` plus `toplevel_array_length_state`. The `type_place_expr` projection for `Builtin` should simplify away separately.
works_when: Applies after unfolding the `Builtin` evaluator one step and assuming `well_typed_expr env (Builtin ty bt es)`. Non-Len needs side conditions from `well_typed_expr_def`/`well_typed_builtin_app_def`, including argument type map and Env MsgGas exclusion if present; Len needs singleton argument facts from the Len typing clause.
evidence:
- tool_output:TO_type_system_rewrite-20260522T073012Z_m42675_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m42674_t001
- episode:E0792

## L1344 scope='C2.4.1' tags=Expr_Builtin,Len,generated-IH,qpat_assum,proof-plumbing
shape: Generated Len IH for `eval_all_type_sound_mutual[Expr_Builtin]` has antecedent `type_check (builtin_args_length_ok bt (LENGTH es)) ... ∧ bt = Len`.
pattern: When applying the generated Len IH in the Expr_Builtin resume, do not consume `bt = Len` or the length-check fact before discharging the IH antecedent. Use `qpat_assum` to rewrite while preserving facts, or instantiate/strip the IH before destructive assumption rewrites. If this still needs many quoted instantiations, factor a local Len-tail adapter helper.
works_when: Applies in the Len branch after unfolding one `evaluate_def`, deriving `builtin_args_length_ok` from `well_typed_builtin_app_length`, and destructing `eval_expr cx (HD es) st`. The same caution applies to any generated IH whose antecedent repeats branch discriminants.
evidence:
- tool_output:TO_type_system_rewrite-20260522T073012Z_m42723_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m42725_t002
- episode:E0793

## L1345 scope='C2.4.1' tags=Expr_Builtin,Len,toplevel_array_length,SArrayV,unprovability_probe
shape: Len branch with `well_typed_builtin_app ty Len ...`, `expr_result_typed env e arg_tv`, and `toplevel_array_length cx arg_tv st = INR ...`.
pattern: Do not use a boundary saying all typed `is_sized_type` values are accepted by `toplevel_array_length`. Fixed-array source types are sized, and typed materialized static-array values (`Value (ArrayV (SArrayV _))`) are rejected by `toplevel_array_length_def` with `TypeError "toplevel_array_length"`. First prove concrete mismatch/reachability probes, then use a precise runtime-shape invariant or repair semantics.
works_when: Applies to the fresh statement-soundness `Expr_Builtin` Len branch and any helper about `toplevel_array_length` under static `is_sized_type` assumptions.
evidence:
- episode:E0794
- tool_output:TO_type_system_rewrite-20260522T073012Z_m42780_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m42795_t001

## L1346 scope='C2.4.1' tags=Expr_Builtin,Len,Name,SArrayV,unprovability_probe,reachability
shape: C2.4.1.b reachability probe for materialized fixed-array value via local `Name`.
pattern: The simplest candidate source of `Value (ArrayV (SArrayV []))` is a local `Name`, not an array literal or storage read. `well_typed_expr env (Name ty id)` only checks `FLOOKUP env.var_types (string_to_num id) = SOME ty`; `eval_expr cx (Name _ id)` reads `lookup_scopes_val` from `st.scopes` and returns `Value v`. Use a singleton `var_types`/scope witness with `entry.type = ArrayTV ... (Fixed 1)` and `entry.value = ArrayV (SArrayV [])` to probe Len reachability.
works_when: Use for C2.4.1.b before constructing contract/global machinery. Full invariants may require `env.type_defs = get_tenv cx`, `current_src = current_module cx`, empty globals/functions, and singleton `st.scopes`.
evidence:
- tool_output:TO_type_system_rewrite-20260522T073012Z_m42812_t003
- tool_output:TO_type_system_rewrite-20260522T073012Z_m42813_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m42818_t002

## L1347 scope='C2.4.1' tags=Len,toplevel_array_length,SArrayV,definition_repair,boundary_lemma
shape: Len soundness stuck on `toplevel_array_length cx arg_tv st = (INR (Error (TypeError ...)), st')` with `expr_result_typed` and fixed-array `is_sized_type` static type.
pattern: If typed `Len` can see `Value (ArrayV (SArrayV sparse))`, do not try to exclude that runtime shape: it is reachable via a local `Name`. Repair `toplevel_array_length_def` with a materialized static-array case returning `(INL (&LENGTH sparse), st)`, then prove a typed runtime no-TypeError boundary and use that in the consumer proof.
works_when: Applies after E0796-style evidence that `well_typed_expr` plus standard runtime invariants allow local fixed-array values represented as `SArrayV`.
evidence:
- episode:E0796
- tool_output:TO_type_system_rewrite-20260522T073012Z_m42855_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m42857_t001

## L1348 scope='C2.4.1' tags=Len,SArrayV,sparse_has_type_length,Len_result_fits_uint256,toplevel_array_length
shape: `Len_result_fits_uint256` or related Len bound goal with `Value (ArrayV (SArrayV sparse))`, assumptions `sparse_has_type tv len sparse`, `SORTED $< (MAP FST sparse)`, and `len * slot < bound`.
pattern: For materialized static arrays, do not reason from the old TypeError catch-all. Use `sparse_has_type_length` to derive `LENGTH sparse <= len`, then chain `LENGTH sparse <= len <= len * slot < bound` with `LESS_EQ_LESS_TRANS`. Keep this arithmetic inside builtin Len boundary theorems, not statement soundness.
works_when: Applies after `toplevel_array_length_def` has a `Value (ArrayV (SArrayV sparse))` success case returning `LENGTH sparse` and the static array typing facts expose `sparse_has_type` plus sorted sparse keys.
evidence:
- episode:E0800
- tool_output:TO_type_system_rewrite-20260522T073012Z_m42893_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m42897_t001
