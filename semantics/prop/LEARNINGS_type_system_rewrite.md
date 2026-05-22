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

## L1189 scope='C2.1.1.4' tags=Expr_Subscript,IH-selection,guarded-IH,resume,replace_text
shape: Expr_Subscript resume raw goal has a guarded index IH followed by an unconditional base IH
pattern: In `Resume eval_all_type_sound_mutual[Expr_Subscript]`, do not apply `first_x_assum drule_all` after splitting the base evaluation. The first IH is guarded by a successful base-eval antecedent and is meant for the index expression `e'` only after the `INL tv1` base branch. Select/label the unconditional base IH explicitly for `e`; after the base-success case, instantiate the guarded index IH with the live `eval_expr cx e st = (INL tv1,st1)` fact.
works_when: After `rpt gen_tac >> strip_tac`, before or after one-step evaluator unfolding, the raw goal contains both IHs for the Subscript constructor: guarded index IH first and base IH second. Verify assumption order with holbuild before using positional selectors.
evidence:
- tool_output:TO_type_system_rewrite-20260521T174852Z_m36683_t001
- tool_output:TO_type_system_rewrite-20260521T174852Z_m36692_t001
- episode:E0631

## L1191 scope='C2.1.1.4' tags=Expr_Subscript,evaluate_subscript,local-helper,ancestor-import,tail-simplification
shape: Expr_Subscript get_Value success tail after `evaluate_subscript ... = INL (INL value)`
pattern: In `vyperTypeStmtSoundnessTheory`, helper theorems from `vyperTypeSoundnessHelpersScript.sml` such as `evaluate_subscript_typed` and `evaluate_subscript_success_not_HashMapRef` are not directly declared in the current ancestor context. For this proof, use the local `_stmt` copies now added near `Resume eval_all_type_sound_mutual[Expr_Subscript]`. In the direct value branch, first prove `~is_HashMapRef result` with `evaluate_subscript_success_not_HashMapRef_stmt`, then strip and simplify the remaining monadic tail equation with `bind_def`/`return_def`; do not expect bare `metis_tac` or `gvs[]` to consume the tail antecedent automatically.
works_when: The live goal has `check_array_bounds ... = (INL (),s)`, `evaluate_subscript ... = INL (INL v)`, `toplevel_value_typed v rtv`, and the tail goal/antecedent still mentions `do check_array_bounds ...; res <- return (INL v); ... od s = (res,st')`. Applies to the direct, non-storage return branch of Expr_Subscript.
evidence:
- tool_output:TO_type_system_rewrite-20260521T174852Z_m36778_t001
- tool_output:TO_type_system_rewrite-20260521T174852Z_m36817_t001
- tool_output:TO_type_system_rewrite-20260521T174852Z_m36826_t001
- episode:E0633

## L1192 scope='C2.1.1.4' tags=Expr_Subscript,monadic-tail,read_storage_slot,bind_def,boundary-lemma
shape: Expr_Subscript storage-return tail after `evaluate_subscript ... = INL (INR y)`
pattern: Do not apply `read_storage_slot_success_type` until the monadic tail equation has been simplified into a concrete `read_storage_slot ... = (INL v, st')` assumption. First consume the exact `do check_array_bounds ...; res <- return (INR y); case res of ... od bounds_st = (res,st')` equation, rewriting with the known `check_array_bounds ... = (INL (),bounds_st)` plus `bind_def`, `ignore_bind_def`, and `return_def`; then split/use the resulting read equation.
works_when: The live context has the storage-return subscript result (`INR y`), `check_array_bounds ... = (INL (),bounds_st)`, and a tail equation/implication that still mentions `read_storage_slot`. Applies both inline and inside a local tail-boundary helper.
evidence:
- tool_output:TO_type_system_rewrite-20260521T174852Z_m36888_t001
- tool_output:TO_type_system_rewrite-20260521T174852Z_m36898_t001
- tool_output:TO_type_system_rewrite-20260521T174852Z_m36905_t001
- episode:E0634

## L1193 scope='C2.1.1.4' tags=Expr_Subscript,evaluate_subscript,TypeError,boundary-lemma,array_index
shape: Expr_Subscript resume reaches `evaluate_subscript ... = INR err` after typed base/index and successful `get_Value`
pattern: Do not handle the `evaluate_subscript ... = INR err` branch by broad inline unfolding in the resume. Use or prove a boundary lemma that explicitly carries typed base (`toplevel_value_typed x tv`, `~is_HashMapRef x`, `evaluate_type ... (expr_type e) = SOME tv`) and typed index evidence. If proving a standalone helper, keep the base value and index value constructor splits separate; tuple/array value cases require `array_index_def` to show the error cannot be `TypeError`.
works_when: Applies after Expr_Subscript base and index IHs have succeeded, `get_Value x' ... = (INL idx,...)`, `check_array_bounds ... = (INL (),...)`, and the evaluator tail has split `evaluate_subscript` into an error branch. The goal is to prove `!msg. err <> TypeError msg`.
evidence:
- tool_output:TO_type_system_rewrite-20260521T174852Z_m36924_t001
- tool_output:TO_type_system_rewrite-20260521T174852Z_m37006_t001
- episode:E0635

## L1194 scope='C2.1.1.4' tags=Expr_Subscript,storage-tail,read_storage_slot,bind_def,TypeError
shape: Storage-return tail after `evaluate_subscript ... = INL (INR y)` and `check_array_bounds ... = (INL (),bounds_st)`
pattern: A repaired `expr_subscript_storage_tail_sound_stmt` should first simplify the exact monadic tail equation with `bind_def`/`ignore_bind_def`/`return_def`, then case-split the resulting `read_storage_slot` equation. Error cases close with `read_storage_slot_error`; the success case uses `read_storage_slot_success_type` and witnesses `rtv` for the expression result type. At the call site, strip the tail implication before `irule` and provide witnesses in theorem order (`bounds_st`, `rtv`, `x`, `x''`, `y`).
works_when: The live context has state/env/account typing for `bounds_st`, `evaluate_type (get_tenv cx) v9 = SOME rtv`, `(case y of ... => tv'=rtv)`, `well_formed_type_value rtv`, and the exact tail equation for returning/reading the storage value.
evidence:
- tool_output:TO_type_system_rewrite-20260521T174852Z_m36920_t001
- tool_output:TO_type_system_rewrite-20260521T174852Z_m36924_t001
- episode:E0635

## L1196 scope='C2.1.1.4' tags=Expr_Subscript,check_array_bounds,TypeError,boundary-lemma
shape: After `check_array_bounds cx x idx st = (INR y,st)` in Expr_Subscript tail
pattern: Use a small boundary lemma (`check_array_bounds_error_not_TypeError_stmt`) rather than unfolding the check-bounds monad at every call site. Its proof needs `oneline check_array_bounds_def` plus `get_storage_backend_no_error`; the error produced by bounds checking is a `RuntimeError`, not a `TypeError`.
works_when: The live goal is `!msg. y <> Error (TypeError msg)` or `no_type_error_result (INR y)` after the monadic tail has simplified to a `check_array_bounds ... = (INR y,st)` assumption.
evidence:
- tool_output:TO_type_system_rewrite-20260521T174852Z_m37071_t001
- tool_output:TO_type_system_rewrite-20260521T174852Z_m37073_t001
- episode:E0636

## L1197 scope='C2.1.1.4' tags=Expr_Subscript,type_place_expr,HashMapT,well_typed_expr,boundary-lemma
shape: Attempted bridge from `type_place_expr env e = SOME vt` to ordinary `well_typed_expr env e` in Expr_Subscript place branch
pattern: Do not formulate the place-branch helper as `type_place_expr env e = SOME vt ==> well_typed_expr env e`. Hashmap places are annotated with `NoneT` (`vtype_annotation_ok (HashMapT _ _) ann_ty = (ann_ty = NoneT)`), while ordinary `well_typed_expr TopLevelName ty` requires a `Type ty` toplevel entry and `ty <> NoneT`. The reusable boundary should instead prove direct eval/result soundness for place-typed expressions, including the `HashMapRef`/`type_place_expr ... = SOME (HashMapT ...)` part of `expr_result_typed`.
works_when: Applies after unfolding `well_typed_expr_def` for `Subscript` and landing in the disjunct with `type_place_expr env e = SOME vt` and `subscript_vtype vt (expr_type e') = SOME (Type ty)`. Especially relevant when the base IH is guarded by `well_typed_expr env e` and cannot be applied.
evidence:
- tool_output:TO_type_system_rewrite-20260521T174852Z_m37087_t003
- tool_output:TO_type_system_rewrite-20260521T174852Z_m37088_t001
- tool_output:TO_type_system_rewrite-20260521T174852Z_m37086_t004

## L1198 scope='C2.1.1.4' tags=Expr_Subscript,type_place_expr,HashMapT,TopLevelName,boundary-lemma
shape: Expr_Subscript place-subscript disjunct with `type_place_expr env e = SOME vt` and no `well_typed_expr env e`
pattern: For the place branch, prove/use direct place-expression eval soundness instead of coercing the base to ordinary expression typedness. TopLevelName/HashMap should be handled with `env_consistent_toplevel_hashmap_static` plus `lookup_global_HashMapVarDecl_returns_HashMapRef`, producing `expr_result_typed` through the HashMapRef side condition of `expr_result_typed_def`. The ordinary `lookup_global_TopLevelName_sound` only covers `well_typed_expr`/`Type ty` entries, so it is insufficient for HashMapT place bases.
works_when: The live assumptions contain `type_place_expr env (TopLevelName ann (src,id)) = SOME (HashMapT kt vt)` or a nested Subscript place branch, along with env/state/context invariants and a successful `eval_expr`/`lookup_global`. Use this before applying the guarded index IH in Expr_Subscript.
evidence:
- tool_output:TO_type_system_rewrite-20260521T174852Z_m37127_t003
- tool_output:TO_type_system_rewrite-20260521T174852Z_m37131_t001
- tool_output:TO_type_system_rewrite-20260521T174852Z_m37156_t001
- tool_output:TO_type_system_rewrite-20260521T174852Z_m37142_t002

## L1199 scope='C2.1.1.4' tags=Expr_Subscript,type_place_expr,mutual-induction,HashMapT,place_expr_result_typed
shape: Expr_Subscript place branch has `type_place_expr env e = SOME vt` but only old base IH guarded by `well_typed_expr env e`
pattern: When a `well_typed_expr (Subscript ...)` proof reaches the alternate `type_place_expr/subscript_vtype` branch, do not try to prove a local bridge to ordinary expression typing or standalone place eval soundness. Strengthen the evaluator mutual expression conjunct with a guarded place-expression postcondition (`type_place_expr env e = SOME vt ==> ... place_expr_result_typed env tv vt`) so nested Subscript place bases use the recursive evaluator IH and indices use the ordinary IH.
works_when: Applies in fresh `vyperTypeStmtSoundnessScript.sml` while proving expression soundness for Subscript/TopLevelName places, especially HashMap locations annotated with `NoneT`. Use after direct `subscript_type_ok` branches are separated from place branches.
evidence:
- episode:E0637
- tool_output:TO_type_system_rewrite-20260521T174852Z_m37197_t001
- tool_output:TO_type_system_rewrite-20260521T174852Z_m37199_t001
- tool_output:TO_type_system_rewrite-20260521T174852Z_m37164_t001
- tool_output:TO_type_system_rewrite-20260521T174852Z_m37175_t001

## L1200 scope='C2.0' tags=For_cons,CHOOSE,boundary-helper,Resume,existential
shape: For_cons / large Resume endpoints with existential or case-premise facts trigger CHOOSE/exact-endpoint failures
pattern: When For_cons proof endpoints expose raw `case (INR exn)` premises, existential packages, or exact visible assumptions, do not retry ACCEPT_TAC/ASSUME/MATCH_MP endpoint tactics in the large Resume/core proof. Move the manipulation into small boundary helpers whose conclusion is the whole suffix or a direct return-exception fact; consume live assumptions with drule/irule and explicit witnesses only at the helper boundary.
works_when: Applies to For_cons evaluator soundness branches after evaluator recursion has produced body-IH facts and popped/pushed invariants, especially under holbuild goalfrag instrumentation.
evidence:
- episode:E0475
- episode:E0503
- episode:E0546
- episode:E0571
- tool_output:TO_type_system_rewrite-20260521T121230Z_m35279_t001

## L1201 scope='C2.0' tags=For_cons,non-loop-exception,irule,explicit-witness
shape: For_cons non-loop exception propagation from body IH
pattern: For non-Continue/non-Break body exceptions, use a full suffix helper that concludes the final `case (INR exn)` return-typing residual. Keep constructor splitting and existential transport outside the core proof; in the caller instantiate helper-only variables explicitly (`body`, `env_after`, `id`, pushed state, `ty`) rather than relying on bare `irule`.
works_when: Use after the For_cons branch has body evaluation `eval_stmts cx body stp = (INR exn, st_body)`, visible pushed-state facts, popped-state facts, and `exn <> ContinueException`, `exn <> BreakException`.
evidence:
- episode:E0546
- episode:E0556
- tool_output:TO_type_system_rewrite-20260521T114716Z_m34784_t001

## L1202 scope='C2.1.1.4.4' tags=expression-IH,place_expr_result_typed,Subscript,proof-refactor
shape: Old expression conjunct has `well_typed_expr` as an antecedent, but Subscript place branch only has `type_place_expr env base = SOME vt`.
pattern: Repair by changing the expression conjunct to first assume only env/state/eval invariants, then conclude a pair of guarded projections: ordinary `well_typed_expr` -> old `expr_result_typed` postcondition, and place `type_place_expr` -> `place_expr_result_typed` postcondition. Consumers should specialize the IH once, split projections, and use the projection matching the static guard.
works_when: Use for Expr_Subscript/TopLevelName place-expression soundness inside `eval_all_type_sound_mutual`; do not use it to justify a standalone place-expression induction.
evidence:
- tool_output:TO_type_system_rewrite-20260521T174852Z_m37207_t003
- tool_output:TO_type_system_rewrite-20260521T174852Z_m37214_t001
- tool_output:TO_type_system_rewrite-20260521T174852Z_m37216_t001

## L1203 scope='C2.1.1.4.4' tags=expression-IH,projection,tactic-timeout,place_expr_result_typed
shape: After strengthening the expression conjunct, a consumer has `first_x_assum drule_all >> strip_tac` and then a full pair `(well_typed_expr ... ==> old_post) /\ (!vt. type_place_expr ... ==> place_post)` in context.
pattern: Do not simplify with the full paired IH in context. Immediately project the needed branch: for ordinary consumers, use `qpat_x_assum `well_typed_expr env e ==> _` (drule_then strip_assume_tac)` and discard the unused `!vt. type_place_expr ...` assumption. Use targeted `rewrite_tac[no_type_error_result_def]` rather than broad `gvs[]` on the resulting large goal.
works_when: Applies to post-refactor statement/expression resumes that consume an expression IH but are not themselves proving a place-expression branch; particularly AssertReason/AnnAssign-style branches.
evidence:
- tool_output:TO_type_system_rewrite-20260521T174852Z_m37227_t001
- tool_output:TO_type_system_rewrite-20260521T174852Z_m37260_t001
- tool_output:TO_type_system_rewrite-20260521T174852Z_m37273_t001

## L1240 scope='C2.1.1.13.3.3' tags=Subscript,Resume,joint-IH,conjunction,proof-shape
shape: Expr_Subscript ordinary Resume branch after `conj_tac`; final conclusion is a conjunction of preservation/no-TypeError/success typing.
pattern: Avoid `rpt strip_tac` that splits the final conjunction into independent goals before evaluator sequencing. Instead, keep/prove the combined ordinary result: unfold `well_typed_expr_def` and `evaluate_def` once, split base/index evaluator results with equations, project IH ordinary conjuncts immediately, then invoke `expr_subscript_ordinary_tail_sound_stmt` to supply the whole conjunction in the all-success tail. Only split conjuncts after the combined fact is available or if a branch is already reduced to a propagated IH fact.
works_when: Use in C2.1.1.13.3.3 and similar expression Resume branches where a local tail helper returns the same conjunction as the Resume conclusion.
evidence:
- tool_output:TO_type_system_rewrite-20260522T073012Z_m38922_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:7060-7070

## L1242 scope='C2.1.1.13.3.3' tags=Subscript,tail-helper,Resume,expr_subscript_ordinary_tail_sound_stmt
shape: All-success ordinary Expr_Subscript tail after `get_Value x' st2 = (INL x'',st2)` and exact monadic tail equation over `x`, `x''`, `x'`, `st2`.
pattern: The ordinary-tail helper matches if invoked as `irule expr_subscript_ordinary_tail_sound_stmt >> simp[] >> qexistsl [`base_tv`,`idx`,`idx_tv`,`tail_st`] >> simp[]`. In the live Resume branch those witnesses were `[x,x'',x',st2]`. Put `simp[]` before `qexistsl` so the non-existential conjuncts are discharged and the remaining existential matches the helper's implicit variables.
works_when: Use when the evaluator equation has already simplified to the successful get_Value tail and assumptions include base/index `expr_result_typed`, post-index invariants, `well_formed_type`, `subscript_type_ok`, and successful `get_Value`.
evidence:
- tool_output:TO_type_system_rewrite-20260522T073012Z_m38985_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m38987_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m38989_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:7112-7117

## L1243 scope='C2.1.1.13.3.3' tags=Subscript,Resume,branching,THEN1,tactical,error-propagation
shape: A `Cases_on`/`Cases_on`-nested Expr_Subscript Resume proof has several remaining subgoals, but a branch-local propagated-error tactic is written as `>> (...)` and holbuild shows it being applied with 3 input goals.
pattern: When proving nested evaluator branches in `Resume eval_all_type_sound_mutual[Expr_Subscript]`, close each case branch explicitly with `>- (...)` before using `>>` for the next common suffix. If holbuild shows a branch tactic with multiple input goals, suspect a missing `>-`/parenthesization issue before debugging assumption selection. Branch-local error propagation should not be written as a shared `>> (...)` suffix unless it really solves all remaining branches.
works_when: Use for nested `Cases_on` proofs where success, get_Value-error, index-error, and base-error branches need different tactics and mutual-IH assumptions are large.
evidence:
- tool_output:TO_type_system_rewrite-20260522T073012Z_m39057_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m39060_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:7101-7130

## L1244 scope='C2.1.1.13.3.3' tags=Subscript,get_Value,subscript_type_ok,int_expr_get_Value_INR_no_type_error,witness-order
shape: Ordinary Subscript get_Value error branch after index success has `expr_result_typed env e' x'`, `get_Value x' st' = (INR y,st')`, and goal `no_type_error_result (INR y)`.
pattern: Invoke `int_expr_get_Value_INR_no_type_error` with existential witnesses in theorem quantifier order `[e', env, st', st', x', expr_type e']`, then prove `is_int_type (expr_type e')` by cases on `expr_type e` using `subscript_type_ok_def`. Do not put `env` first; holbuild reports the post-`irule` existential order as `∃e env st st' tv ty ...`.
works_when: Applies to ordinary `well_typed_expr` Subscript branches with `subscript_type_ok`, not place/projection branches with `subscript_vtype`.
evidence:
- tool_output:TO_type_system_rewrite-20260522T073012Z_m39003_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m39005_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:4192-4202

## L1245 scope='C2.1.1.13.3.3' tags=Subscript,well_typed_expr_def,static-inversion,branching,THEN1
shape: After unfolding `well_typed_expr_def` for `well_typed_expr env (Subscript v9 e e')`, the proof needs the ordinary static disjunct but the theorem also contains a place/projection static disjunct.
pattern: Do not rely on `strip_tac >- (...)` immediately after `simp_tac(srw_ss())[Once well_typed_expr_def]` to isolate the ordinary Subscript static branch. If the consumer is only the ordinary half, use a controlled static inversion/split or a local helper that exposes the ordinary facts; keep the place branch as an explicit placeholder for C2.1.1.13.4.
works_when: Applies inside `Resume eval_all_type_sound_mutual[Expr_Subscript]` ordinary branch, where the final goal remains an implication over `well_typed_expr env (Subscript ...)` and sibling component owns the place/projection case.
evidence:
- tool_output:TO_type_system_rewrite-20260522T073012Z_m39094_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m39100_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:7070-7073

## L1246 scope='C2.1.1.13.3.3' tags=Subscript,well_typed_expr_def,static-inversion,get_Value,subscript_type_ok
shape: Ordinary Expr_Subscript static inversion and get_Value-error branch after `well_typed_expr_def` exposes ordinary/place disjunction
pattern: For the ordinary Subscript Resume conjunct, explicitly discharge the `well_typed_expr env (Subscript ...)` antecedent, move it to the goal, rewrite only that antecedent with `CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [well_typed_expr_def]))`, then use the first branch for ordinary facts and leave the place branch to the sibling. In the ordinary get_Value-error branch use `int_expr_get_Value_INR_no_type_error` with witnesses `[e', env, st', st', x', expr_type e']`, deriving `is_int_type (expr_type e')` by cases on `expr_type e` and `subscript_type_ok_def`.
works_when: Use in C2.1.1.13.3.3-style ordinary `well_typed_expr` Subscript branches where the final goal is ordinary `expr_result_typed`, not place/projection typing.
evidence:
- episode:E0685
- tool_output:TO_type_system_rewrite-20260522T073012Z_m39135_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m39140_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:7068-7143

## L1267 scope='C2.1.1.13.4.2.1' tags=Expr_Subscript,base-success-helper,get_Value,branch-local,tail-helper
shape: Inside `expr_subscript_ordinary_base_success_sound_stmt`, after base and index success, context has branch-local `get_Value x st2 = (INL idx,st3)` plus `do ... od st3 = (res,st')`.
pattern: For the base-success helper, move the simplified `(case get_Value x st2 of ...) = (res,st')` equality to assumptions before splitting `get_Value`. After `Cases_on get_Value` and `Cases_on val_res`, the INL branch should be solved locally with `get_Value_state` and `expr_subscript_ordinary_tail_sound_stmt`; the INR branch should use `get_Value_state` and `expr_subscript_index_get_Value_INR_no_type_error_stmt`. If the goal still mentions the full outer `eval_expr (Subscript ...)` case, the proof has regressed to the old adapter boundary.
works_when: Applies after unfolding `eval_expr cx (Subscript ...)` inside the base-success helper and rewriting with `eval_expr cx e st = (INL base_tv,st1)`, then using the index IH for `eval_expr cx e' st1 = (INL x,st2)`.
evidence:
- tool_output:TO_type_system_rewrite-20260522T073012Z_m39983_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m39987_t001
- episode:E0701

## L1268 scope='C2.1.1.13.4.2' tags=Expr_Subscript,boundary-helper,wrapper,simp-timeout,helper-antecedent
shape: Calling a Subscript boundary helper leaves a large conjunction of assumptions already present in the wrapper context; broad `simp[]` times out.
pattern: For Subscript adapter wrappers, specialize the boundary helper, use `disch_then irule`, then discharge the helper antecedent with explicit conjunct splitting and assumption discharge (`rpt conj_tac >> first_assum ACCEPT_TAC`) after extracting any case-simplified typing fact with a targeted `mp_tac >> simp_tac(srw_ss())[] >> strip_tac`. Avoid `(impl_tac >- simp[])` or `gvs[]` on the whole antecedent.
works_when: The wrapper has already split the base evaluation, instantiated the relevant IH, and all helper assumptions are present as separate assumptions except for a case-expression typing fact such as `case INL base_tv of ...`.
evidence:
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40049_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40051_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40057_t001
- episode:E0703

## L1269 scope='C2.1.1.13.4.2.1' tags=Expr_Subscript,get_Value,INR,irule,existential-witness
shape: After `get_Value x st2 = (INR val_err,st2)`, goal is `no_type_error_result (INR val_err)` with `expr_result_typed env e' x` and `subscript_type_ok ...` in assumptions.
pattern: Use `irule expr_subscript_index_get_Value_INR_no_type_error_stmt` with explicit witnesses in the existential order shown by the goal (`e`, `e'`, `env`, `st2`, `st2`, `x`, `v9`), then `simp[]`. This avoids brittle `drule_all`/`ACCEPT_TAC` paths that may leave an apparently identical assumption unusable.
works_when: Inside the ordinary base-success helper after `get_Value_state` has rewritten the error state to the same state and the index result typing is available from the index IH.
evidence:
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40035_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40037_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40041_t001
- episode:E0702

## L1270 scope='C2.1.1.13.4.3' tags=Expr_Subscript,projection-helper,postcondition,tactic-timeout,boundary-lemma
shape: After applying `expr_subscript_place_projection_branch_sound_stmt`, context contains a large implication from the exact subscript tail equality to the desired place-typed postcondition.
pattern: Do not immediately `Cases_on res >> simp[]` with the large helper implication still present. First derive a named intermediate postcondition by `first_x_assum irule` and targeted one-step evaluator rewrite with the known base-evaluation equality; then split `res` and convert the `INL` place-typed fact using `place_expr_result_typed_expr_result_typed_stmt`.
works_when: Use in place-as-ordinary Subscript adapters where the projection helper conclusion is needed to prove ordinary expression result typing and the source has `eval_expr cx (Subscript ...) st = (res,st')` plus `eval_expr cx e st = (INL base_tv,st1)`.
evidence:
- episode:E0706
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40087_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40092_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:7443-7457

## L1271 scope='C2.1.1.13.4.3a' tags=BaseTarget_Subscript,bind_def,performance,proof_refactor
shape: BaseTarget_Subscript successful base-target branch after `Cases_on bt_res` and `PairCases_on x`.
pattern: Replace broad `simp[bind_def]` with bounded `rewrite_tac[bind_def, return_def]` after pair destruction; this exposes the monadic branch without timing out in the large mutual-IH context.
works_when: Use only after the evaluator has already been unfolded and `eval_base_target cx bt st = (INL (x0,x1),st1)` is in context. Do not add `AllCaseEqs()` or unfold `evaluate_def` again.
evidence:
- episode:E0705
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40072_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40082_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:6073-6075

## L1272 scope='C2.1.1.13.4.4' tags=Expr_Subscript,audit,cheat,FAIL_TAC,Resume,integration
shape: Post-integration audit for a Resume with adjacent proved local adapters and later unrelated cheated resumes in the same file.
pattern: When closing a local integration/audit component, combine a successful theory build with a grep audit and source readback. Interpret grep hits by source region: later scheduled Resume cheats after the completed block do not block closure if the component-local Resume/adapters contain no `cheat` or `FAIL_TAC`. Fix stale comments that still mention temporary cheats before closure.
works_when: Use only when the PLAN component's scope is a local Resume/helper region and later cheats are already covered by separate scheduled components. Cite both the build and grep/readback evidence in the closure.
evidence:
- episode:E0708
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40115_t002
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40115_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40113_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:7472-7539

## L1273 scope='C2.2' tags=Expr_Attribute,evaluate_attribute,struct_has_type,ALOOKUP,boundary_lemma
shape: Need to prove Attribute field projection from `value_has_type (StructTV ftypes) sv` and static field lookup `ALOOKUP ftypes id = SOME field_tv`.
pattern: First prove a local `struct_has_type` ALOOKUP bridge by induction over parallel field/type alists: `struct_has_type ftypes fields /\ ALOOKUP ftypes id = SOME field_tv ==> ?field_v. ALOOKUP fields id = SOME field_v /\ value_has_type field_tv field_v`. Then `evaluate_attribute_value_has_type` is just a case split on `sv`, `simp[evaluate_attribute_def,value_has_type_def]`, and the bridge. This keeps `evaluate_attribute_def` out of the mutual Resume proof.
works_when: Use when the runtime value is already known to have a concrete `StructTV ftypes` type and the static typing side has been bridged to an executable `ALOOKUP ftypes id` fact (e.g. via `attribute_type_evaluates`).
evidence:
- episode:E0709
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40140_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:7541-7563

## L1274 scope='C2.2' tags=Expr_Attribute,attribute_type_evaluates,expr_result_typed,get_Value,boundary_lemma,Resume
shape: Need to package the successful `eval_expr cx (Attribute ty e id)` tail after base expression succeeds and `expr_result_typed env e base_tv` is available.
pattern: Prove/use a helper over the whole Attribute evaluation equality rather than inlining in the Resume. Inside the helper: unfold `eval_expr` for `Attribute` once; rewrite with `eval_expr cx e st = (INL base_tv,st1)`; unfold `expr_result_typed_def`/`expr_runtime_typed_def`; case-split `expr_type e`, not the runtime `type_value`; `attribute_type_def` + `evaluate_type_def` force the StructT branch and produce `StructTV (ZIP (MAP FST fields,tvs))`. From `toplevel_value_typed base_tv (StructTV ...)`, derive `base_tv = Value sv`; then use `attribute_type_evaluates` and `evaluate_attribute_value_has_type` to close no-TypeError and success typing.
works_when: Applies to C2.2.3-style Attribute integration when the base expression IH has already supplied successful-result typing and preservation facts, and the static typing side has `attribute_type env.type_defs (expr_type e) id = SOME ty`. Keep this inside the helper; the final Resume should just expose premises and call it.
evidence:
- episode:E0710
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40195_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:7565-7601

## L1279 scope='C2.3.3' tags=Expr_Pop,Append,target_runtime_typed,assign_target_no_type_error,assignable_context,proof-pattern
shape: Need to prove Pop assignment branch after successful `eval_base_target` under dynamic `type_place_target`.
pattern: Use the existing `Append` statement branch as the local proof template: instantiate the base-target IH, convert its INL facts into `target_runtime_typed env cx st1 (BaseTarget bt) ty (BaseTargetV loc sbs)` by unfolding `target_runtime_typed_def`/`target_value_shape_def`/`well_typed_atarget_def`; derive operation runtime typing and shape; derive `assign_target_assignable_context` via `target_runtime_typed_imp_assignable_context`; then apply assignment-target soundness/preservation wrappers. For Pop, substitute `stmt_assign_operation_runtime_typed_Pop_from_dynamic_array` and `stmt_assign_operation_matches_target_shape_Pop_BaseTargetV`.
works_when: Applies after the Pop premise provides `type_place_target env bt = SOME (Type (ArrayT elem_ty (Dynamic n)))` and the base-target IH returns `base_target_value_shape` plus `location_runtime_typed`/`target_path_type`.
evidence:
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40316_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40314_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40315_t003

## L1280 scope='C2.3.3' tags=Expr_Pop,assignable_type,well_formed_type,evaluate_type,PopOp,boundary-lemma
shape: Need `assignable_type env.type_defs (ArrayT elem_ty (Dynamic n))` in Pop branch after deriving only `evaluate_type env.type_defs elem_ty = SOME elem_tv`.
pattern: Do not treat `assignable_type` as a mere well-formedness fact. For `ArrayT elem bd`, `assignable_type_def` requires `well_formed_type (ArrayT elem bd)` AND recursively `assignable_type elem`; an `evaluate_type elem = SOME elem_tv` fact only proves well-formedness. If a consumer only has dynamic target typing/path facts, either strengthen the static typing/extraction interface to include assignability or use/prove a specialized assignment boundary that does not require generic `assignable_type`.
works_when: Applies to fresh-stack Pop/assignment statement proofs using `assign_target_no_type_error` or `assign_target_sound_mutual` side conditions after dynamic-array target typing repair.
evidence:
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40396_t001
- source:semantics/prop/vyperTypeSystemScript.sml:224-238
- source:semantics/prop/vyperTypeSystemScript.sml:507-508

## L1281 scope='C2.3.4' tags=well_typed_expr_def,Pop,existential,conjunctive-witness,metis_tac
shape: After strengthening a defining clause from `?n. P n` to `?n. P n /\ Q n`, an old extraction lemma for just `?n. P n` no longer closes by plain `simp[Once def]`.
pattern: Use `simp[Once def] >> metis_tac[]` for the weaker projection lemma, and add a separate strong extraction lemma preserving the full conjunctive witness. This keeps old consumers working while exposing the stronger interface to new consumers.
works_when: Applies to HOL4 definition repairs where an existential witness gains extra conjuncts and existing projection lemmas should remain available.
evidence:
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40420_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40421_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40422_t001

## L1282 scope='C2.3.5' tags=PopOp,assign_result,evaluate_subscripts,popped_value,boundary-lemma
shape: Need successful `assign_result tv PopOp old subs = (INL popped, st')` to expose `popped = SOME v` and `value_has_type elem_tv v`.
pattern: Factor Pop result typing below `assign_target`: prove `evaluate_subscripts_leaf_well_typed`, `popped_value_well_typed`, then `assign_result_pop_success_some_typed` with premise `leaf_type tv subs = ArrayTV elem_tv (Dynamic n)`. In the final proof, after simplifying `assign_result_def`, add `leaf_type tv subs <> NoneTV` explicitly and use `evaluate_subscripts_leaf_well_typed`; do not supply an existential witness after `gvs[]` has simplified the goal to element typing.
works_when: Applies to fresh assignment-target Pop proofs for scoped/ordinary storage/immutable paths that call `assign_result` after successful subscript assignment.
evidence:
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40457_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40462_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40466_t001
- episode:E0723

## L1283 scope='C2.3.5' tags=HOL4,evaluate_subscripts,induction,case-split,array_index
shape: Induction over `evaluate_subscripts` Int-subscript branch leaves `array_index tv av i = SOME v` and `evaluate_subscripts elem_tv v subs = INL v'`.
pattern: In `evaluate_subscripts` leaf-typing induction, split the subscript value before the current value: `Cases_on v >> gvs[evaluate_subscripts_def, AllCaseEqs()]`, then case-split `tv` and use `array_index_has_type`. If you case-split the original value after simplification, HOL reports no variable named `a` because the goal has already specialized it to `ArrayV av`.
works_when: Applies when porting/evolving leaf-typing lemmas over `evaluate_subscripts` from retired helpers into the fresh stack.
evidence:
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40458_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40460_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40466_t001

## L1284 scope='C2.3.5' tags=PopOp,assign_target,theorem-placement,TopLevelVar,branch-helper
shape: Exported `assign_target_pop_success_some_typed` needs TopLevelVar helper lemmas to discharge Value/HashMapRef/ArrayRef branches.
pattern: If the assign-target Pop boundary proof uses helpers such as `lookup_global_storage_Value_typed`, `top_level_storage_value_leaf_evaluate_type`, or ArrayRef/HashMap branch facts, place the exported theorem after those helpers (currently after `Finalise assign_target_sound_mutual` is safe) or factor/move the branch helper earlier. Placing it immediately after `assign_result_pop_success_some_typed` makes later helper names unavailable.
works_when: Applies to lifting lower-level `assign_result` Pop facts through `assign_target` in `vyperTypeStatePreservationScript.sml`.
evidence:
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40514_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40521_t001
- episode:E0724

## L1285 scope='C2.3.5' tags=PopOp,ScopedVar,ImmutableVar,assign_result,leaf_type
shape: ScopedVar/ImmutableVar branches of `assign_target_pop_success_some_typed` after unfolding `assign_target_def`.
pattern: For scoped/immutable Pop branches, derive `place_leaf_typed` via `target_runtime_typed_place_leaf_typed`, rewrite `place_leaf_typed_def`/`place_leaf_path_typed_def` to get `evaluate_type ... (ArrayT elem_ty (Dynamic n)) = SOME (leaf_type root_tv (REVERSE sbs))`, then use `gvs[evaluate_type_def]` to get `leaf_type root_tv (REVERSE sbs) = ArrayTV elem_tv (Dynamic n)`. Combine old-value typing/well-formedness from runtime consistency and finish with `assign_result_pop_success_some_typed`.
works_when: Applies to non-storage-direct branches that call `assign_result root_tv PopOp old (REVERSE sbs)` after assignment.
evidence:
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40523_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40531_t001
- episode:E0724

## L1286 scope='C2.3.5' tags=PopOp,TopLevelVar,StorageVarDecl,assign_result,lookup_global_storage_Value_typed
shape: TopLevelVar Value/StorageVarDecl branch of `assign_target_pop_success_some_typed` after unfolding `assign_target_def`.
pattern: Case-split `p`, extract the layout slot from `IS_SOME`, then use `lookup_global_storage_Value_typed` for old-value typing and `top_level_storage_value_leaf_evaluate_type` plus `evaluate_type_def` to derive `leaf_type root_tv (REVERSE sbs) = ArrayTV elem_tv (Dynamic n)`. Finish with `assign_result_pop_success_some_typed`.
works_when: Applies when `lookup_global` returns `INL (Value old_v)` and the declaration is `StorageVarDecl`; the branch calls `assign_result root_tv PopOp old_v (REVERSE sbs)` after `set_global` succeeds.
evidence:
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40547_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40597_t001
- episode:E0725

## L1287 scope='C2.3.5' tags=PopOp,TopLevelVar,HashMapRef,place_leaf_path_typed_split_leaf_type,lookup_global_HashMapRef
shape: HashMapRef branch of `assign_target_pop_success_some_typed` after `split_hashmap_subscripts` and successful storage read/write.
pattern: Use a fresh `lookup_global_HashMapRef` helper to align the runtime `HashMapRef` with `HashMapVarDecl`; combine with `top_level_HashMap_decl` and `target_path_type_Type_place_leaf_typed`. After `gvs[place_leaf_typed_def, place_leaf_path_typed_def]`, apply `place_leaf_path_typed_split_leaf_type` to connect `evaluate_type (ArrayT elem_ty (Dynamic n))` to `leaf_type base_tv remaining`, then finish with `read_storage_slot_success_type` and `assign_result_pop_success_some_typed`.
works_when: Applies to TopLevelVar HashMapRef Pop paths where `assign_target` goes through `compute_hashmap_slot`, `read_storage_slot`, ordinary `assign_subscripts`, write, and `assign_result`.
evidence:
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40578_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40595_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40597_t001
- episode:E0725

## L1288 scope='C2.3.5' tags=PopOp,ArrayRef,resolve_array_element,drule,branch-helper
shape: TopLevelVar ArrayRef branch of `assign_target_pop_success_some_typed` needs to connect root `leaf_type (ArrayTV elem_tv' bd) (REVERSE sbs)` to resolved `leaf_type final_tv remaining`.
pattern: Add/use simple non-nested wrapper lemmas around `resolve_array_element_leaf_type_sc` and `resolve_array_element_well_formed_sc`, then apply them with `drule`/`drule_all` to the live `resolve_array_element ... = INL (...)` assumption. Direct `metis_tac` or `MATCH_MP` on the nested original helper is brittle/timeouts in the large ArrayRef goal. After the leaf equality, `gvs[leaf_type_def]` splits ordinary vs direct dynamic Pop paths.
works_when: Applies in fresh state-preservation ArrayRef assignment proofs after `PairCases_on x` and `gvs[...]` have exposed the `resolve_array_element` success assumption and storage read/write/assign_result assumptions.
evidence:
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40646_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40668_t001
- episode:E0726

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
