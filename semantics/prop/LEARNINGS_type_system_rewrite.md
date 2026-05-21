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

## L1095 scope='C2.3.3' tags=Resume,CHOOSE,existential,For_cons,case-premise
shape: Suspended `Resume` proof; IH assumption is `case (INR y) of ... => ?env_exn. ...`; final goal needs case-form return typing.
pattern: In this suspended For_cons Resume, simplifying the IH case premise to an existential is not sufficient if the suffix later closes existential/conjunct obligations by exact assumption acceptance. `ACCEPT_TAC`/`first_assum ACCEPT_TAC` on theorem objects derived from existential stripping can still trigger HOL_ERR CHOOSE during validation. Prefer a helper/drule path that consumes the top-level existential theorem or factor the entire suffix outside the Resume.
works_when: Use when holbuild shows CHOOSE after apparently trivial exact-assumption closure in `eval_all_type_sound_mutual[For_cons]` ordinary-exception suffix.
evidence:
- tool_output:TO_type_system_rewrite-20260519T123242Z_m32207_t001
- tool_output:TO_type_system_rewrite-20260519T123242Z_m32214_t001
- tool_output:TO_type_system_rewrite-20260519T123242Z_m32216_t002

## L1100 scope='ForConsOrdinaryExceptionCaseHelperSubtree.IntegrateForConsSuffix.PatchResumeSuffix.2.2.1.2' tags=For_cons,qpat_x_assum,type-constraint,case-premise
shape: Pattern-matching the `case (INR y : unit + exception)` body premise in a context with an existing value variable `v`.
pattern: When selecting the `case (INR y : unit + exception)` premise in the For_cons suffix, do not write the INL branch as `INL (v:unit)` if `v` is already bound as a value in the context; the quotation parser imposes the wrong type constraint. Use a fresh unit branch variable such as `u`.
works_when: Use in targeted `qpat_x_assum`/case-premise selection in `vyperTypeStmtSoundnessScript.sml` around the For_cons ordinary-exception Resume.
evidence:
- tool_output:TO_type_system_rewrite-20260519T123242Z_m32491_t001
- tool_output:TO_type_system_rewrite-20260519T123242Z_m32493_t001

## L1105 scope='ForConsOrdinaryExceptionCaseHelperSubtree.IntegrateForConsSuffix.PatchResumeSuffix.2.2.1.2.2.1.1.2.2.1' tags=Resume,suspend,CHOOSE,For_cons,proof-boundary
shape: Final For_cons ordinary-exception suffix inside `Resume eval_all_type_sound_mutual[For_cons]` has exact assumptions but endpoint tactics or nested suspend raise HOL_ERR CHOOSE.
pattern: When a suspended `Resume` fragment raises CHOOSE on exact assumptions/tautological implications, do not keep changing endpoint tactics or insert a nested `suspend` at the same point. Move the proof boundary outside the resumed fragment, e.g. prove the whole case as an ordinary helper theorem with explicit IH premises, then make the Resume case a shallow wrapper.
works_when: Applies after evidence shows the suffix facts are semantically present in the goal context and helper lemmas prove the final invariant, but `ACCEPT_TAC`/`simp[]`/`DISCH_THEN`/nested `suspend` fail inside the Resume proof boundary.
evidence:
- episode:E0475
- episode:E0476
- episode:E0477
- tool_output:TO_type_system_rewrite-20260520T094007Z_m32827_t001

## L1106 scope='ForConsOrdinaryExceptionCaseHelperSubtree.IntegrateForConsSuffix.PatchResumeSuffix.2.2.1.2.2.1.1.2.2.1.2.1' tags=no_control,bind_INR,same_blocks,performance
shape: Goal `do read_storage_slot; lift_sum(assign_subscripts ...); write_storage_slot; assign_result ... od s = (INR exc,s') ==> no_control_exc exc` repeated under many type constructors.
pattern: Factor the common monadic do-block into a standalone no-control helper proved by `bind_INR` and primitive no-control lemmas, rather than splitting on `type_value`/`assign_operation` and expanding all cases in the caller.
works_when: The residual exception source is a fixed do-chain whose component functions already have no-control theorems; no typing/state hypotheses should be needed.
evidence:
- tool_output:TO_type_system_rewrite-20260520T094007Z_m32866_t001
- tool_output:TO_type_system_rewrite-20260520T094007Z_m32870_t001
- tool_output:TO_type_system_rewrite-20260520T094007Z_m32879_t001

## L1107 scope='ForConsOrdinaryExceptionCaseHelperSubtree.IntegrateForConsSuffix.PatchResumeSuffix.2.2.1.2.2.1.1.2.2.1.2.1' tags=holbuild,performance,AllCaseEqs,case_split
shape: Proof-performance hotspot after `gvs[AllCaseEqs()]` on evaluator/type-value cases.
pattern: If `AllCaseEqs` plus constructor splitting leaves many similar `INR -> no_control_exc` subgoals, stop expanding and introduce a boundary lemma for the repeated monadic suffix. More cases can increase to hundreds of goals and exceed holbuild's tactic timeout.
works_when: The displayed residuals share the same do-block modulo constructor wrappers or operation cases.
evidence:
- tool_output:TO_type_system_rewrite-20260520T094007Z_m32868_t001
- tool_output:TO_type_system_rewrite-20260520T094007Z_m32870_t001

## L1108 scope='ForConsOrdinaryExceptionCaseHelperSubtree.IntegrateForConsSuffix.PatchResumeSuffix.2.2.1.2.2.1.1.2.2.1.2' tags=no_control,res_tac,performance,direct_premise
shape: Goal `no_control_exc exc` with assumptions `∀s exc st'. eval_exprs cx es s = (INR exc,st') ⇒ no_control_exc exc` and `eval_exprs cx es s0 = (INR exc0,st0)`.
pattern: Do not use `res_tac` in large no-control contexts when an exact universal premise and exact matching equation are present. Specialize the premise directly on the displayed state/exception/state variables (or `first_x_assum drule` on the matching equation) and simplify only the resulting fact.
works_when: The error branch is generated by decomposing a monadic bind and the HOL goal already contains a no-control premise for that exact subcomputation.
evidence:
- tool_output:TO_type_system_rewrite-20260520T094007Z_m32920_t001
- tool_output:TO_type_system_rewrite-20260520T094007Z_m32926_t002

## L1109 scope='ForConsOrdinaryExceptionCaseHelperSubtree.IntegrateForConsSuffix.PatchResumeSuffix.2.2.1.2.2.1.1.2.2.1.2.2.2' tags=For_cons,IH-selection,qpat_x_assum,eval_stmts
shape: Multiple universal IH assumptions with similar binders (`!stp res_body st_body. _`) in `eval_for_cons_type_sound_core`.
pattern: Select the body statement IH by matching distinctive antecedents, e.g. `env_consistent (extend_local env id ty F) cx stp /\ ... /\ eval_stmts cx body stp = ... ==> _`, not by binder names or `_` conclusion. The broad pattern matched the recursive-tail IH shape and generated an impossible `env_consistent env cx stp` obligation.
works_when: Use this in the For_cons helper/Resume context where both body and recursive-tail IH premises are live and have overlapping quantifier names.
evidence:
- tool_output:TO_type_system_rewrite-20260520T094007Z_m32953_t001
- tool_output:TO_type_system_rewrite-20260520T094007Z_m32955_t001
- episode:E0482

## L1110 scope='ForConsOrdinaryExceptionCaseHelperSubtree.IntegrateForConsSuffix.PatchResumeSuffix.2.2.1.2.2.1.1.2.2.1.2.2.1' tags=no_control,ExtCall,res_tac,premise-specialization
shape: Goal `no_control_exc exc` with exact assumptions `∀s exc st'. eval_exprs cx es s = (INR exc,st') ==> no_control_exc exc` and `eval_exprs cx es s = (INR exc,st')`.
pattern: Avoid `res_tac` in large ExtCall/no-control contexts. Use targeted specialization: `qpat_x_assum `∀s exc st'. eval_exprs cx es s = (INR exc,st') ⇒ no_control_exc exc` (qspecl_then [`s`,`exc`,`st'`] mp_tac) >> simp[]`.
works_when: The branch is an immediate `eval_exprs` failure path and the equation variables are exactly the current `s`, `exc`, `st'`.
evidence:
- tool_output:TO_type_system_rewrite-20260520T094007Z_m32936_t001
- tool_output:TO_type_system_rewrite-20260520T094007Z_m32937_t001
- episode:E0481

## L1112 scope='ForConsOrdinaryExceptionCaseHelperSubtree.IntegrateForConsSuffix.PatchResumeSuffix.2.2.1.2.2.1.1.2.2.1.2.2.2' tags=For_cons,suffix,CHOOSE,case-premise,holbuild
shape: After `irule for_cons_ordinary_exception_full_suffix_from_case_premise`, residual is a conjunction ending in `∃env_after id st_body ty. case INR y of ...`.
pattern: Preserve the full ordinary-exception case premise instead of destructing to `env_exn`; destructing creates a CHOOSE-sensitive final `return_exception_typed env_exn ret_ty y` endpoint. Early conjuncts can be closed locally (`simp[]` for state/account/env facts, `fs[no_type_error_result_def]` for `no_type_error_result (INR y)`). If exact acceptance of the full case premise fails, factor a helper rather than destructing it.
works_when: Use in `eval_for_cons_type_sound_core` tail after the proof prefix has assumptions `no_type_error_result (INR y)`, full `case (INR y : unit + exception) of ...`, `state_well_typed stfinal`, `accounts_well_typed stfinal.accounts`, and `env_consistent env cx stfinal`.
evidence:
- tool_output:TO_type_system_rewrite-20260520T094007Z_m33024_t001
- tool_output:TO_type_system_rewrite-20260520T094007Z_m33033_t001
- episode:E0485

## L1113 scope='ForConsOrdinaryExceptionCaseHelperSubtree.IntegrateForConsSuffix.PatchResumeSuffix.2.2.1.2.2.1.1.2.2.1.2.2.2' tags=For_cons,ACCEPT_TAC,ASSUME,CHOOSE,endpoint
shape: Exact displayed assumption equals current atomic goal in `eval_for_cons_type_sound_core` suffix.
pattern: Do not assume exact-assumption tactics are safe under this holbuild-instrumented proof boundary. `qpat_x_assum ... ACCEPT_TAC` and `ACCEPT_TAC (ASSUME ...)` both raised HOL_ERR/CHOOSE on exact goals; prefer changing the goal shape or using small simplification where it demonstrably closes the subgoal.
works_when: Applies to the current For_cons ordinary-exception suffix proof under holbuild goalfrag instrumentation; may not generalize globally.
evidence:
- tool_output:TO_type_system_rewrite-20260520T094007Z_m33017_t001
- tool_output:TO_type_system_rewrite-20260520T094007Z_m33028_t001
- tool_output:TO_type_system_rewrite-20260520T094007Z_m33033_t001
- episode:E0484
- episode:E0485

## L1114 scope='ForConsOrdinaryExceptionCaseHelperSubtree.IntegrateForConsSuffix.PatchResumeSuffix.2.2.1.2.2.1.1.2.2.1.2.2.2.2' tags=For_cons,INR_witness,irule,premise_order,existential
shape: After `irule for_cons_ordinary_exception_full_suffix_from_INR_witness` in `eval_for_cons_type_sound_core`, the first subgoal is `∃id st_body ty env_exn. ... return_exception_typed ... y`, not `no_type_error_result (INR y)`.
pattern: Discharge the witness premise first by moving the full `case (INR y : unit + exception) of ...` assumption to the goal, `simp[]` to expose `∃env_exn. ...`, `strip_tac`, then provide witnesses `id`, `st_body`, `ty`, `env_exn`. Only then close no-error with `fs[no_type_error_result_def]` and final state/account/env facts with `simp[]`.
works_when: Use in the ordinary-exception tail after assumptions include no-error, final state/account/env facts, and the full body-IH case premise for `INR y`. Avoid exact acceptance of the full case premise.
evidence:
- tool_output:TO_type_system_rewrite-20260520T110618Z_m33061_t001
- tool_output:TO_type_system_rewrite-20260520T110618Z_m33063_t001
- tool_output:TO_type_system_rewrite-20260520T110618Z_m33065_t001
- episode:E0488

## L1115 scope='ForConsOrdinaryExceptionCaseHelperSubtree.IntegrateForConsSuffix.PatchResumeSuffix.2.2.1.2.2.1.1.2.2.1.2.2.2.2' tags=For_cons,timeout,env_consistent,gvs
shape: Core proof prefix fact `env.type_defs = get_tenv cx` from `env_consistent env cx st` timed out with `fs[env_consistent_def, env_context_consistent_def]`.
pattern: Use `gvs[env_consistent_def, env_context_consistent_def]` instead of `fs[...]` for this local fact; it advanced holbuild past the timeout to the intended tail patch.
works_when: Applies at line ~3756 of `eval_for_cons_type_sound_core`, before proving pushed-state facts.
evidence:
- tool_output:TO_type_system_rewrite-20260520T110618Z_m33061_t001
- episode:E0488

## L1116 scope='ForConsOrdinaryExceptionCaseHelperSubtree.IntegrateForConsSuffix.PatchResumeSuffix.2.2.1.2.2.1.1.2.2.1.2.2.2.2' tags=For_cons,INR_witness,bundle_helper,premise_order,case_premise
shape: `irule for_cons_ordinary_exception_full_suffix_from_INR_witness_bundle` inside `eval_for_cons_type_sound_core` ordinary-exception tail.
pattern: Generated subgoals are ordered: witness existential, `state_well_typed stfinal`, `no_type_error_result (INR y)`, accounts, env-consistency. Preserve the full `case (INR y)` assumption with `qpat_assum ... mp_tac` when deriving the witness, because the final env-consistency helper may need the same premise again.
works_when: Use after `qmatch_goalsub_abbrev_tac `state_well_typed stfinal`` and after assumptions include no-error, the full case premise, state/accounts/env facts for `stfinal`, and popped env-consistency helper premises.
evidence:
- tool_output:TO_type_system_rewrite-20260520T125121Z_m33146_t001
- tool_output:TO_type_system_rewrite-20260520T125121Z_m33148_t001
- tool_output:TO_type_system_rewrite-20260520T125121Z_m33150_t001
- tool_output:TO_type_system_rewrite-20260520T125121Z_m33151_t001
- episode:E0489

## L1117 scope='ForConsOrdinaryExceptionCaseHelperSubtree.IntegrateForConsSuffix.PatchResumeSuffix.2.2.1.2.2.1.1.2.2.1.2.2.2.2' tags=For_cons,CHOOSE,exact_endpoint,helper_boundary
shape: Trivial-looking final goals in instrumented `eval_for_cons_type_sound_core` tail, e.g. matching `state_well_typed ...` assumption or reflexive pair equality.
pattern: Do not spend attempts on endpoint tactics (`ACCEPT_TAC`, `REFL_TAC`, `simp[]`, `REWRITE_TAC [assumption]`) when holbuild reports CHOOSE/no theorem proved on a syntactically trivial goal. Move the endpoint behind a theorem/helper boundary or restructure so the exact goal is not exposed.
works_when: Applies specifically to the ordinary-exception tail where holbuild instrumentation has repeatedly failed on exact/trivial endpoints despite matching assumptions.
evidence:
- tool_output:TO_type_system_rewrite-20260520T125121Z_m33112_t001
- tool_output:TO_type_system_rewrite-20260520T125121Z_m33117_t001
- tool_output:TO_type_system_rewrite-20260520T125121Z_m33135_t001
- tool_output:TO_type_system_rewrite-20260520T125121Z_m33138_t001
- episode:E0489

## L1120 scope='ForConsOrdinaryExceptionCaseHelperSubtree.FinishEvalForConsOrdinaryExceptionSuffix.UseDirectCaseBundleTail' tags=For_cons,case_premise,residual_bundle,CHOOSE,boundary_lemma
shape: For_cons ordinary-exception suffix with visible no-error, full `case (INR y : value + exception)` premise, and final stfinal invariants; residual existential helper leaves `?id' st_body' ty' env_exn...` goals.
pattern: Use a full-suffix boundary theorem whose antecedents are the visible high-level assumptions (`no_type_error_result`, full case premise, and final invariants). In this source the intended boundary is `for_cons_ordinary_exception_full_suffix_from_case_bundle_direct >> simp[]`. Avoid intermediate residual existential bundle helpers; their conclusion order is fragile under `irule` and triggers CHOOSE/extract_thm endpoint failures when manually destructed.
works_when: Applies after the For_cons body result has been reduced to `INR y`, Continue/Break cases are eliminated, `stfinal` is introduced, and the body IH has produced the full exceptional case premise. If a residual existential bundle appears, the proof has dropped below the intended abstraction level.
evidence:
- episode:E0491
- tool_output:TO_type_system_rewrite-20260520T132249Z_m33382_t001
- tool_output:TO_type_system_rewrite-20260520T132249Z_m33380_t001

## L1121 scope='ForConsOrdinaryExceptionCaseHelperSubtree.FinishEvalForConsOrdinaryExceptionSuffix.UseBundledCasePremiseTail' tags=For_cons,case_premise,bundled_theorem,irule,antecedent_order,CHOOSE
shape: For_cons ordinary-exception suffix after `qmatch_goalsub_abbrev_tac stfinal`, with visible noerr, full `case (INR y : value + exception)` premise, and final state/account/env facts.
pattern: Use `for_cons_ordinary_exception_full_suffix_from_case_bundle`, not the curried `_direct` wrapper, in the main theorem. Plain `irule ... >> simp[]` may not close: holbuild showed generated antecedent subgoals in the order `accounts_well_typed stfinal.accounts`, `no_type_error_result (INR y)`, `state_well_typed stfinal`, `env_consistent env cx stfinal`, then `?env_after id st_body ty. case INR y of ...`. Solve simple conjuncts by `simp[]`/`fs[no_type_error_result_def]`, then instantiate the outer existential with visible `env_after`, `id`, `st_body`, `ty` and discharge using the existing case premise. Do not destruct the inner `env_exn` in the large theorem.
works_when: Applies only in the ordinary non-Continue/non-Break `INR y` branch of `eval_for_cons_type_sound_core` after final `stfinal` invariants and the body-IH case premise are visible. If the inner `env_exn` existential becomes the active proof obligation, stop and package it in a helper rather than using CHOOSE in the main theorem.
evidence:
- tool_output:TO_type_system_rewrite-20260520T132249Z_m33470_t001
- tool_output:TO_type_system_rewrite-20260520T132249Z_m33474_t001
- tool_output:TO_type_system_rewrite-20260520T132249Z_m33475_t001
- episode:E0492

## L1124 scope='ForConsOrdinaryExceptionCaseHelperSubtree.FinishEvalForConsOrdinaryExceptionSuffix.PatchEvalForConsCoreTail' tags=For_cons,visible_bundle,case_premise,boundary_lemma,goalfrag,INR_witness
shape: For_cons ordinary-exception tail after `stfinal` expansion, with final suffix proved by a helper whose antecedent includes a `case INR y of ...` premise.
pattern: A visible-bundle helper removes antecedent-only `env_after/id/ty` existentialization, but if its bundled antecedent still contains the `case INR y` body premise, applying it backward leaves the same fragile case-premise subgoal in the large theorem. Prefer a helper over the already-simplified INR witness triple (or a popped-state `_from_INR_witness_bundle` variant) so the final consumer does not need to select/simplify the case expression.
works_when: Applies in `eval_for_cons_type_sound_core` ordinary non-continue/non-break exception branch after assumptions include no-error, popped-state facts, and body case premise. Use only for designing the next helper; do not use it as a reason to destruct `env_exn` manually in the large theorem.
evidence:
- episode:E0498
- episode:E0499
- tool_output:TO_type_system_rewrite-20260520T132249Z_m33611_t001
- tool_output:TO_type_system_rewrite-20260520T132249Z_m33621_t001

## L1125 scope='ForConsOrdinaryExceptionCaseHelperSubtree.FinishEvalForConsOrdinaryExceptionSuffix.PatchEvalForConsCoreTailWithResidualWitness' tags=For_cons,ReturnException,env_extends,return_exception_typed,goalfrag,timeout
shape: For_cons ordinary-exception tail after `simp[]`, with goal reduced to `return_exception_typed env ret_ty y`.
pattern: A direct `Cases_on y` can avoid the unstable `case INR y` premise entirely. Non-ReturnException constructors close with `simp[return_exception_typed_def]`; only the ReturnException branch needs transport of `value_runtime_typed` from the body exception witness environment back to `env`. For that branch, prefer existing env-extension return-typing helpers or a targeted projection over broad `gvs[env_extends_def, extend_local_def]`.
works_when: Use after popped-state/state/account/env/no-error conjuncts have simplified away and the remaining suffix is only `return_exception_typed env ret_ty y`; assumptions include the body case premise and no-error for `INR y`.
evidence:
- tool_output:TO_type_system_rewrite-20260520T132249Z_m33684_t001
- tool_output:TO_type_system_rewrite-20260520T132249Z_m33689_t001
- tool_output:TO_type_system_rewrite-20260520T132249Z_m33691_t002
- episode:E0502

## L1127 scope='ForConsOrdinaryExceptionCaseHelperSubtree' tags=For_cons,ReturnException,boundary_lemma,CHOOSE,large_context
shape: For_cons ordinary-exception suffix has visible existential/case premise but local assumption/existential tactics fail in large theorem.
pattern: Move existential/case-premise manipulation into small boundary lemmas placed before `eval_for_cons_type_sound_core`; the large theorem should consume a theorem whose conclusion matches the whole suffix and should not use raw CHOOSE/qpat/ACCEPT_TAC on the body case premise.
works_when: Use for the For_cons ordinary-exception branch after `eval_stmts cx body stp = (INR exn, st_body)` and the final suffix needs popped state/account/env, no-TypeError, and return typing.
evidence:
- episode:E0503
- episode:E0505
- tool_output:TO_type_system_rewrite-20260520T132249Z_m33776_t001

## L1128 scope='ForConsOrdinaryExceptionCaseHelperSubtree.FinishEvalForConsOrdinaryExceptionSuffix.AddBodyExceptionProjectionHelper' tags=For_cons,body-IH,ReturnException,boundary_lemma,case-premise,env_extends
shape: Need `return_exception_typed env ret_ty exn` for a For_cons body result `eval_stmts cx body stp = (INR exn, st_body)` without consuming the final raw `case INR ...` premise in `eval_for_cons_type_sound_core`.
pattern: Prove a small body-IH projection helper: specialize the universal body-soundness hypothesis at `stp`, `INR exn`, and `st_body`; discharge pushed-state preconditions; simplify the resulting `case (INR exn)`; then transport the existential `env_exn` typing back to `env` using the existing return-exception boundary (`for_cons_return_exception_typed_from_body_ex` or `return_exception_typed_extend_local_env_extends`). In the large theorem, retain the universal body IH with non-destructive `qpat_assum` and apply this projection helper instead of selecting the raw case premise.
works_when: Use in the For_cons ordinary-exception tail after the body equation and pushed-state invariants are available, especially when raw final case-premise selection in the large theorem causes CHOOSE/FIRST_ASSUM/extract_thm failures.
evidence:
- tool_output:TO_type_system_rewrite-20260520T132249Z_m33819_t001
- episode:E0507
- tool_output:TO_type_system_rewrite-20260520T132249Z_m33814_t001

## L1130 scope='ForConsOrdinaryExceptionCaseHelperSubtree.FinishEvalForConsOrdinaryExceptionSuffix.PatchEvalForConsCoreTailWithBodyProjection' tags=For_cons,ReturnException,boundary_lemma,large_context,CHOOSE,premise_order
shape: In `eval_for_cons_type_sound_core`, a small helper applies but exact endpoints such as `env_consistent env cx st` or a large-conjunction `simp[]` fail in the final ReturnException branch.
pattern: For this For_cons large theorem, make consumer helpers require already-derived pushed facts (`env.type_defs = get_tenv cx`, `env_consistent (extend_local env id ty F) cx stp`) and order premises so the tail can discharge them sequentially. Avoid late original-env exact endpoints and avoid `simp[]` over the whole helper conjunction; use explicit `conj_tac` in theorem-statement order or escalate to a full-tail bundled helper.
works_when: Use after `Cases_on y` in the final ReturnException branch, with retained body IH, `stp = pushed-state`, and `eval_stmts cx body stp = (INR (ReturnException v'),st_body)` available.
evidence:
- episode:E0514
- tool_output:TO_type_system_rewrite-20260520T132249Z_m33920_t001
- tool_output:TO_type_system_rewrite-20260520T132249Z_m33934_t001
- tool_output:TO_type_system_rewrite-20260520T132249Z_m33945_t001

## L1131 scope='ForConsOrdinaryExceptionCaseHelperSubtree.FinishEvalForConsOrdinaryExceptionSuffix.PatchEvalForConsCoreTailDirectBodySoundness' tags=For_cons,CHOOSE,boundary-lemma,holbuild,exact-endpoint
shape: In `eval_for_cons_type_sound_core`, a helper application leaves a conjunction or existential package whose conjuncts are all visible as assumptions, but endpoint tactics fail with HOL_ERR CHOOSE.
pattern: Do not keep varying exact endpoint tactics in this For_cons tail. If `irule`/IH specialization leaves atomic visible-assumption subgoals or an existential-package conjunction, factor a helper that consumes the package/the specialized IH result and directly concludes the final `return_exception_typed ...`; the large theorem should not destruct the package or prove trivial conjuncts locally.
works_when: Use after specializing the body IH in the final `ReturnException` branch, especially around source lines ~4205-4216, where holbuild goalfrag raises CHOOSE on tautological endpoints.
evidence:
- tool_output:TO_type_system_rewrite-20260520T175243Z_m34024_t001
- tool_output:TO_type_system_rewrite-20260520T175243Z_m34048_t001
- tool_output:TO_type_system_rewrite-20260520T175243Z_m34056_t001

## L1132 scope='ForConsOrdinaryExceptionCaseHelperSubtree.FinishEvalForConsOrdinaryExceptionSuffix.PatchEvalForConsCoreTailWithBodyResultHelper' tags=For_cons,ReturnException,body-IH,boundary-helper,MATCH_MP
shape: Final For_cons ReturnException tail after body IH specialization
pattern: Use `for_cons_body_result_return_exception_typed` by theorem-value application to the whole specialized body-IH conjunction. Avoid `cj 4`, `irule for_cons_return_exception_typed_from_body_ex`, and local existential package construction/destruction in `eval_for_cons_type_sound_core`.
works_when: After the local body IH has been specialized to `stp`, `INR (ReturnException v')`, and `st_body`, and its antecedent is discharged from assumptions `env_consistent (extend_local env id ty F) cx stp`, `state_well_typed stp`, `accounts_well_typed stp.accounts`, and `eval_stmts cx body stp = (INR (ReturnException v'), st_body)`.
evidence:
- tool_output:TO_type_system_rewrite-20260520T175243Z_m34083_t001
- tool_output:TO_type_system_rewrite-20260520T175243Z_m34084_t001

## L1137 scope='C2.0.2' tags=For_cons,ReturnException,non-loop-exception,boundary-lemma,CHOOSE,unit+exception
shape: Large For-cons core proof reaches propagated exception residual for `INR y` with popped invariants, pushed invariants, body evaluation equality, body IH, and `y <> ContinueException`, `y <> BreakException`.
pattern: Do not split the exception or apply ReturnException-only helpers inside `eval_for_cons_type_sound_core`. Prove an external `for_cons_non_loop_exception_suffix` whose conclusion is the whole final residual with `(case (INR exn : unit + exception) of INL _ => T | INR exn0 => return_exception_typed env ret_ty exn0)`. Inside the helper, split on `exn`; discharge non-return constructors by `return_exception_typed_def` and the `ReturnException v` case by `for_cons_return_exception_suffix`.
works_when: Use when holbuild/goalfrag shows `Thm.CHOOSE` in the large caller on exact-assumption/trivial implication endpoints after applying a narrower suffix helper. The caller should only instantiate the wider helper; all constructor/case/existential work stays outside the core proof.
evidence:
- episode:E0546
- tool_output:TO_type_system_rewrite-20260520T182357Z_m34481_t001
- tool_output:TO_type_system_rewrite-20260520T182357Z_m34483_t001
- episode:E0547

## L1140 scope='C2.0.2.2' tags=For_cons,body-IH,projection-helper,conjunction,existential,CHOOSE,GEN,boundary-lemma
shape: For-cons helper specializes body IH at `(stp, INR exn, st_body)` and the goal is the full specialized conjunction, while its conjuncts appear as assumptions after `strip_tac`.
pattern: Do not close this area by whole-goal theorem acceptance (`first_assum ACCEPT_TAC`, explicit `ASSUME`/`LIST_CONJ`, `MATCH_MP`) and do not open/rebuild the exception existential. Specialize the body IH, discharge antecedents, `strip_tac`, then construct the final conjunction subgoal-by-subgoal (`rpt conj_tac` with per-conjunct assumption closure), keeping the case/existential branch packaged.
works_when: Applies to C2.0.2.2.1/C2.0.2.2.2 For-cons helper lemmas after body-IH specialization. If exact whole-conjunction endpoints fail, use subgoal-level construction; if even per-conjunct construction fails, escalate for a direct suffix-consumes-IH interface.
evidence:
- episode:E0551
- episode:E0552
- tool_output:TO_type_system_rewrite-20260521T114716Z_m34732_t001
- tool_output:TO_type_system_rewrite-20260521T114716Z_m34730_t001

## L1141 scope='C2.0.2.3' tags=For_cons,irule,existential-witness,suffix-helper,core-patch
shape: Core proof applies a helper whose conclusion matches but whose variables (`body`, `env_after`, `id`, `stp`, `ty`) appear mainly in antecedents, leaving existential helper-parameter goals after bare `irule`.
pattern: When applying `for_cons_non_loop_exception_suffix` in `eval_for_cons_type_sound_core`, do not rely on `irule` to infer all parameters. Immediately supply explicit witnesses for caller-only parameters, especially `body`, `env_after`, `id`, the pushed state, and `ty`, then simplify `Abbr`stp`` and discharge remaining local assumptions from the existing core context.
works_when: Use after the core branch has substituted `res = INR y`, `st' = st_body with scopes := TL st_body.scopes`, and has assumptions for pushed `stp`, body evaluation, popped invariants, and `y <> ContinueException/BreakException`.
evidence:
- tool_output:TO_type_system_rewrite-20260521T114716Z_m34784_t001
- tool_output:TO_type_system_rewrite-20260521T114716Z_m34786_t002
- episode:E0556

## L1142 scope='C2.0.2.3' tags=For_cons,body-IH,endpoint-validation,helper-interface
shape: Core proof must prove a helper antecedent identical to a universally quantified body-IH consequent, but exact acceptance/simplification fails in the mutual-proof context.
pattern: When `for_cons_non_loop_exception_suffix` is applied in `eval_for_cons_type_sound_core`, proving the final body-IH antecedent inline by specializing the existing IH can enter a brittle endpoint-validation state. If exact-looking goals remain after `mp_tac`/`strip_tac` or `goal_assum $ drule_at Any`, factor the antecedent into a caller-shaped helper/corollary instead of retrying local acceptance tactics.
works_when: Applies after the core branch has derived `res = INR y`, supplied explicit witnesses to `for_cons_non_loop_exception_suffix`, and the remaining goal is the helper's universal body-IH antecedent for arbitrary `stp0 res_body st_body0`.
evidence:
- tool_output:TO_type_system_rewrite-20260521T121230Z_m34860_t001
- tool_output:TO_type_system_rewrite-20260521T121230Z_m34870_t001
- tool_output:TO_type_system_rewrite-20260521T121230Z_m34872_t001
- episode:E0557

## L1143 scope='C2.0.2.3.1' tags=For_cons,projected-helper,sum_case_def,existential,return_exception_typed
shape: Projected helper with premise `case (INR exn) of ... => ?env_exn. ...` and conclusion requiring `return_exception_typed env ret_ty exn`.
pattern: If direct proof of a case-expression projected helper is brittle after `sum_case_def`, first prove an explicit existential-form helper taking `env_exn` and the three existential conjuncts as separate premises, then prove the case-expression compatibility theorem by `rpt strip_tac >> gvs[sum_case_def] >> irule explicit_helper >> qexists_tac ...`. This avoids reconstructing universal body-IH facts in the core proof.
works_when: Use for the For-cons non-loop exception suffix after body IH has produced an actual exceptional projection and the only semantic step is `return_exception_typed_extend_local_env_extends`.
evidence:
- tool_output:TO_type_system_rewrite-20260521T121230Z_m34952_t001
- tool_output:TO_type_system_rewrite-20260521T121230Z_m34954_t001
- episode:E0559

## L1144 scope='C2.0.2.3.2' tags=For_cons,existential,CHOOSE,sum_case_def,projected-helper
shape: Goal/assumption are identical-looking existential facts after simplifying `case (INR y : unit + exception) of ...`, but `ACCEPT_TAC`, `disch_then ACCEPT_TAC`, `metis_tac[]`, or direct `ASSUME` fail with CHOOSE-origin errors.
pattern: In the For-cons core branch, avoid exact existential endpoint acceptance. After reducing the helper premise with `simp[sum_case_def]`, move/simplify the body-IH case fact, destruct it with `qx_choose_then` (or an equivalent explicit existential elimination), then rebuild the existential goal with `qexists_tac` and solve conjuncts from assumptions.
works_when: Use when consuming the actual projected body-IH exceptional fact for `INR y` in `eval_for_cons_type_sound_core`; the first four premises of `for_cons_non_loop_exception_suffix_projected` are already solved from assumptions and only the existential projected-case premise remains.
evidence:
- tool_output:TO_type_system_rewrite-20260521T121230Z_m35020_t001
- tool_output:TO_type_system_rewrite-20260521T121230Z_m35031_t001
- tool_output:TO_type_system_rewrite-20260521T121230Z_m35033_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:4548-4566

## L1146 scope='C2.0.2.3.2.1' tags=For_cons,CHOOSE,boundary-helper,body-IH,existential
shape: A suspended core proof needs to pass a body-IH premise whose conclusion differs only by alpha names in a `case res_body of INL ... | INR ... ?env_exn ...` branch.
pattern: Do not prove this body-IH premise inside `eval_for_cons_type_sound_core`. Prove standalone transport lemmas over arbitrary `res_body` first (`for_cons_body_ih_conclusion_transport`, then `for_cons_body_ih_premise_transport`) and have the core proof use the full-IH wrapper by name. In the standalone `INR` case, provide the existing `env_exn` witness explicitly.
works_when: Applies after the direct suffix helper `for_cons_non_loop_exception_suffix` is the intended endpoint and all non-body-IH premises are visible/dischargeable, but local acceptance/simplification of the body-IH premise fails with CHOOSE-origin validation.
evidence:
- episode:E0567
- tool_output:TO_type_system_rewrite-20260521T121230Z_m35149_t001
- tool_output:TO_type_system_rewrite-20260521T121230Z_m35154_t001

## L1148 scope='C2.0.2.3.2.1' tags=For_cons,CHOOSE,boundary-helper,body-IH,existential,sum_case
shape: For-cons endpoint needs `return_exception_typed env ret_ty y` but the only direct evidence is body-IH `case (INR y) of ... ?env_exn ...`.
pattern: Do not consume the concrete `case (INR y)` existential inside `eval_for_cons_type_sound_core`; in the suspended endpoint, even alpha-equivalent assumptions, explicit witnesses, trivial conjunctions, and `P ==> P` can fail with CHOOSE/Q_TAC validation. Instead prove a standalone non-existential helper that specializes the body IH at `(stp, INR y, st_body)` and concludes `return_exception_typed env ret_ty y`, then apply that helper in the endpoint.
works_when: Applies to the For-cons ordinary non-loop exception branch after pushed-state facts and concrete `eval_stmts cx body stp = (INR y, st_body)` are available. The helper must copy the body-IH premise shape from `eval_for_cons_type_sound_core` and have no existential/case in its conclusion.
evidence:
- episode:E0571
- tool_output:TO_type_system_rewrite-20260521T121230Z_m35279_t001
- tool_output:TO_type_system_rewrite-20260521T121230Z_m35277_t001
