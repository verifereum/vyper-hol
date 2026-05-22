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

## L1226 scope='C2.1.1' tags=Resume,well_typed_expr,type_place_expr,ordinary-projection,place-projection,Subscript
shape: Expression Resume goal concludes `(well_typed_expr env (Ctor ...) ==> ordinary_soundness) /\ (!vt. type_place_expr env (Ctor ...) = SOME vt ==> place_soundness)`, while old proof starts by selecting `well_typed_expr` as an assumption.
pattern: For each expression constructor Resume, split the joint ordinary/place conclusion before consuming constructor typing. In the ordinary half, `strip_tac` the `well_typed_expr` antecedent and only then unfold the constructor typing/evaluator definitions. In the place half, reason separately from the `type_place_expr ... = SOME vt` antecedent: use a targeted NONE lemma only for genuinely non-place constructors, and use place-specific IH/facts for constructors such as Subscript.
works_when: Applies to `eval_all_type_sound_mutual` expression Resume branch-local repairs. Verified for IfExp and StructLit; current Subscript failure has the same proof-order shape but likely a non-vacuous place projection.
evidence:
- episode:E0663
- episode:E0664
- tool_output:TO_type_system_rewrite-20260521T174852Z_m38283_t003
- tool_output:TO_type_system_rewrite-20260521T174852Z_m38291_t001

## L1227 scope='C2.1.1' tags=Resume,expression,place_projection,Subscript,proof_order
shape: Expression Resume goal concludes `(well_typed_expr env (Ctor ...) ==> ordinary) /\ (!vt. type_place_expr env (Ctor ...) = SOME vt ==> place)`
pattern: Always split the joint expression conclusion before consuming constructor typing. For non-place constructors the place half may close by targeted `type_place_expr` contradiction; for place-capable constructors such as Subscript, strip the `type_place_expr ... = SOME vt` assumption and use the appropriate place IH/boundary lemmas.
works_when: Applies inside `eval_all_type_sound_mutual` expression Resume branches after the strengthened joint ordinary/place invariant. Avoids premature `qpat_x_assum`/`drule_all` failures when the typing premise is still an implication antecedent.
evidence:
- tool_output:TO_type_system_rewrite-20260521T174852Z_m38291_t001
- episode:E0663
- episode:E0664
- tool_output:TO_type_system_rewrite-20260521T174852Z_m38309_t001

## L1235 scope='C2.1.1.13' tags=Subscript,place_projection,place_expr_result_typed,HashMapT,helper
shape: Separate Subscript place projection under `type_place_expr env (Subscript ...) = SOME result_vt` needs successful evaluator result typed as a place.
pattern: Do not derive the place projection from the expression-half helper alone. Add/use a helper whose success conclusion is `place_expr_result_typed env tv result_vt`; this is necessary for nested `HashMapT` place results, which are not ordinary expression results. Keep `evaluate_subscript_def`/nested hashmap unfolding inside that helper, not in the mutual Resume.
works_when: Use for C2.1.1.13.2/C2.1.1.13.4 and any later place-capable expression whose place projection can return HashMapT references.
evidence:
- tool_output:TO_type_system_rewrite-20260522T073012Z_m38687_t001
- episode:E0677
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:6759-6865

## L1237 scope='C2.1.1.13' tags=holbuild,checkpoint,performance,rw,IfExp,Subscript,cold-build
shape: A checkpoint-clean `vyperTypeStmtSoundnessTheory` rebuild later fails before the active Subscript helper at an earlier theorem whose proof starts with broad `rw[]` over a mutual-IH implication.
pattern: Treat checkpoint-discard cold-build failures as real source proof-performance obligations. If an earlier helper times out on broad `rw[]`, get PLAN coverage/authorization and replace only the broad opener with controlled stripping/targeted simplification before continuing the semantic helper. Do not rely on stale checkpoints to validate newly inserted boundary lemmas.
works_when: Use when holbuild invalidates checkpoints after local source edits and exposes an earlier timeout unrelated to the active semantic proof, especially in mutual evaluator soundness scripts.
evidence:
- tool_output:TO_type_system_rewrite-20260522T073012Z_m38720_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m38724_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:6228-6263

## L1238 scope='C2.1.1.13' tags=Subscript,place_expr_result_typed,HashMapT,evaluate_subscript,boundary_helper
shape: Subscript place-projection helper with base `HashMapT kt result_vt` and conclusion `place_expr_result_typed env tv result_vt`.
pattern: In the HashMap place case, derive the base annotation with `type_place_expr_annotation_ok_stmt`, then split on `result_vt`. If `result_vt = Type ty`, unfold `evaluate_subscript_def` to a storage-read tail and prove the returned `Value` with `read_storage_slot_success_type` plus `place_expr_result_typed_def`. If `result_vt = HashMapT kt vt`, the evaluator returns a `HashMapRef` directly; simplify the local do-tail with `ignore_bind_def`, `check_array_bounds_hashmap_stmt`, and `evaluate_subscript_def`, then finish by `place_expr_result_typed_def`.
works_when: Use for Expr_Subscript proofs where the static fact is `type_place_expr env e = SOME base_vt` and `subscript_vtype base_vt (expr_type e') = SOME result_vt`, and the consumer wants place typing of the successful result.
evidence:
- episode:E0680
- tool_output:TO_type_system_rewrite-20260522T073012Z_m38784_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:6868-6979

## L1239 scope='C2.1.1.13' tags=Subscript,Resume,joint-IH,assumption-selection,ordinary-branch
shape: Expr_Subscript ordinary Resume after applying base expression IH: context contains both `well_typed_expr env e ==> ordinary` and `!vt. type_place_expr env e = SOME vt ==> place` projections.
pattern: Project or label the ordinary IH immediately after applying the base IH; do not rely on later exact `qpat_x_assum` patterns over the long conclusion. If the place projection is not needed in the ordinary-base branch, discard it while it is top-stack/known-position, then discharge the ordinary implication with the existing `well_typed_expr env e`.
works_when: Use in `eval_all_type_sound_mutual` expression Resume branches with joint ordinary/place IH conclusions, especially Subscript where both projections may be present and goals are large.
evidence:
- tool_output:TO_type_system_rewrite-20260522T073012Z_m38823_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m38827_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m38829_t001

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

## L1247 scope='C2.1.1.13' tags=Subscript,type_place_expr,static-inversion,gvs,Resume
shape: Expr_Subscript place conjunct with assumption `type_place_expr env (Subscript v9 e e') = SOME vt` in mutual Resume.
pattern: For the place/projection conjunct, move the `type_place_expr env (Subscript ...) = SOME vt` assumption to the goal and use `simp_tac(srw_ss())[Once well_typed_expr_def, AllCaseEqs()]` to expose `well_typed_expr env e'`, `type_place_expr env e = SOME vt'`, `subscript_vtype vt' (expr_type e') = SOME vt`, and `vtype_annotation_ok vt v9`. Do not follow with broad `gvs[]`; it can time out under the mutual-IH context. Strip/simplify only the exact evaluator-tail implication before proceeding.
works_when: Use in `eval_all_type_sound_mutual[Expr_Subscript]` place/projection branch after C2.1.1.13.2 helper exists and the goal is the second/place conjunct.
evidence:
- tool_output:TO_type_system_rewrite-20260522T073012Z_m39177_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m39175_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m39203_t001

## L1248 scope='C2.1.1.13' tags=Subscript,Resume,place-conjunct,strip_tac,branch-structure
shape: `eval_all_type_sound_mutual[Expr_Subscript]` second/place conjunct after finishing ordinary conjunct; goal is `!vt. type_place_expr env (Subscript ...) = SOME vt ==> ...`.
pattern: Open the place conjunct with `gen_tac >> strip_tac`, not `rpt strip_tac`. `rpt strip_tac` over-strips the quantified place conjunct and can leave the proof in the wrong branch structure with many spurious goals. After `gen_tac >> strip_tac`, static inversion and the projection helper operate on the intended single `vt` place obligation.
works_when: Use in expression Resume branches where the theorem conclusion is a conjunction of ordinary and place obligations and the second conjunct is universally quantified over `vt`.
evidence:
- tool_output:TO_type_system_rewrite-20260522T073012Z_m39240_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m39249_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:7144-7166

## L1250 scope='C2.1.1.13' tags=Subscript,Resume,projection-helper,adapter,proof-interface,goal-shape
shape: Expr_Subscript place/projection `Resume` successful get_Value branch still has two full outer branch goals after direct helper application.
pattern: If direct use of `expr_subscript_place_projection_tail_sound_stmt` from the `Resume` leaves the full outer place-conjunct implication, do not add more inline instantiation/simplification. Factor a local consumer adapter whose conclusion matches the branch (or whole evaluator-tail implication) and have that adapter invoke the projection-tail helper. Long `Q.SPECL` lists and post-helper case splits inside the `Resume` are proof-interface smells here.
works_when: Use after static inversion has exposed `type_place_expr env e = SOME vt'`, `subscript_vtype vt' (expr_type e') = SOME vt`, base/index IH facts, and successful `get_Value`, but holbuild still reports two high-level goals / `first subgoal not solved`.
evidence:
- episode:E0688
- tool_output:TO_type_system_rewrite-20260522T073012Z_m39349_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:7188-7196

## L1252 scope='C2.1.1.13.4' tags=Subscript,Resume,adapter,well_formed_type,proof-interface,performance
shape: Expr_Subscript place/projection adapter use has all branch facts except `well_formed_type env.type_defs v9`, and proving that static fact inline under the Resume times out.
pattern: When a branch adapter leaves only a static annotation well-formedness conjunct under a huge mutual Resume context, do not prove it inline with `Cases_on`/`gvs`. Either derive the static fact before entering the large adapter antecedent via a small local lemma over `type_place_expr`/`vtype_annotation_ok`, or reformulate the adapter to consume the original static `type_place_expr env (Subscript ...) = SOME vt` assumption and internalize the well-formedness bridge.
works_when: Use after static inversion of `type_place_expr env (Subscript v9 e e') = SOME vt` has exposed `well_typed_expr env e'`, `type_place_expr env e = SOME vt'`, `subscript_vtype vt' (expr_type e') = SOME vt`, and `vtype_annotation_ok vt v9`, but the projection branch adapter still requires `well_formed_type env.type_defs v9`.
evidence:
- tool_output:TO_type_system_rewrite-20260522T073012Z_m39500_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m39509_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:7247-7251

## L1253 scope='C2.1.1.13.4' tags=Subscript,type_place_expr,well_formed_type,static-bridge,expr_induction,adapter
shape: Expr_Subscript place/projection adapter requires `well_formed_type env.type_defs ann` but the Resume only has `type_place_expr env (Subscript ann e e') = SOME result_vt` plus `vtype_annotation_ok result_vt ann`.
pattern: Move annotation well-formedness out of the huge mutual Resume into a small static bridge: prove `type_place_expr` returns a `well_formed_vtype` under `env_consistent`, prove `vtype_annotation_ok` on a well-formed value type implies the annotation type is `well_formed_type`, then use those facts to discharge the adapter antecedent. Do not prove this by unfolding definitions in the Resume.
works_when: Use when a place/projection consumer adapter is otherwise proved but its use site lacks a direct `well_formed_type` fact for the syntactic annotation.
evidence:
- episode:E0692
- tool_output:TO_type_system_rewrite-20260522T073012Z_m39531_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m39536_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m39547_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:6727-6769

## L1254 scope='C2.1.1.13.4' tags=Subscript,static-bridge,well_formed_type,proof-interface,narrow-helper
shape: Expr_Subscript adapter needs `well_formed_type env.type_defs ann`, but a broad `well_typed_expr_well_formed_type` helper opens unrelated Pop/target obligations.
pattern: For the Subscript place/projection adapter, prefer an exact static bridge over global expression/target well-formedness theorems: consume `type_place_expr env (Subscript ann base idx) = SOME vt` and `vtype_annotation_ok vt ann` (plus `env_consistent`) to derive `well_formed_type env.type_defs ann`. If a proposed helper introduces Pop or `type_place_target` cases, it is too broad for this leaf.
works_when: Use when discharging `expr_subscript_place_projection_branch_sound_stmt`/tail-helper antecedents in `eval_all_type_sound_mutual[Expr_Subscript]`, especially after the static inversion already exposes `vtype_annotation_ok vt ann`.
evidence:
- tool_output:TO_type_system_rewrite-20260522T073012Z_m39588_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m39592_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m39596_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:6753-6818

## L1255 scope='C2.1.1.13.4' tags=Subscript,Resume,adapter,implication,performance,simp-timeout
shape: After applying a branch adapter in `eval_all_type_sound_mutual[Expr_Subscript]`, goal is `(tail_eq ==> desired) ==> desired` with the exact evaluator-tail equality already in assumptions.
pattern: Do not finish adapter applications with broad `simp[]`; it can time out on the full monadic tail. After discharging the adapter antecedent manually, consume the adapter result as an implication with `disch_then irule >> first_assum ACCEPT_TAC` when the exact tail equality is live.
works_when: Use after `expr_subscript_place_projection_branch_sound_stmt` or a similar branch adapter has been instantiated, its static/IH conjuncts are discharged, and the remaining theorem on the goal is an implication from the exact evaluator-tail equality to the desired soundness conclusion.
evidence:
- tool_output:TO_type_system_rewrite-20260522T073012Z_m39621_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m39623_t001
- episode:E0693
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:7302-7306

## L1257 scope='C2.1.1.13.4' tags=Subscript,static-split,adapter,proof-interface,risk-mismatch
shape: A broad Expr_Subscript ordinary helper rewrites `well_typed_expr (Subscript ...)` internally and then base-error branches still show the full preservation/no-TypeError goal.
pattern: Split the static `well_typed_expr (Subscript ...)` disjunction before entering branch helpers. Use separate adapters for the ordinary static branch (`well_typed_expr e`, `well_typed_expr e'`, `subscript_type_ok ...`) and the place-as-ordinary static branch (`type_place_expr e = SOME base_vt`, `subscript_vtype ... = SOME (Type ann)`). Do not repair the broad helper with more quoted tail equalities; its statement is the proof-interface problem.
works_when: Use in `eval_all_type_sound_mutual[Expr_Subscript]` or similar evaluator cases where one syntactic expression typing rule has multiple static alternatives but the runtime evaluator skeleton is shared.
evidence:
- episode:E0695
- tool_output:TO_type_system_rewrite-20260522T073012Z_m39725_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m39727_t001

## L1258 scope='C2.1.1.13.4' tags=Expr_Subscript,well_typed_expr,static-split,adapter
shape: Expr_Subscript ordinary branch should be split by static typing alternative before local tail proof
pattern: For the Expr_Subscript ordinary conjunct, split `well_typed_expr env (Subscript v9 e e')` at the Resume boundary with `Once well_typed_expr_def`/`AllCaseEqs()` and call one of two adapters: an ordinary-static adapter taking `well_typed_expr env e`, `well_typed_expr env e'`, `well_formed_type`, and `subscript_type_ok`; or a place-as-ordinary adapter taking `type_place_expr env e = SOME base_vt` and `subscript_vtype base_vt (expr_type e') = SOME (Type v9)`. Do not rewrite the static disjunction inside one broad helper.
works_when: Current C2.1.1.13.4 replacement plan after E0695; applies to `eval_all_type_sound_mutual[Expr_Subscript]` and local adapters in `vyperTypeStmtSoundnessScript.sml`.
evidence:
- episode:E0695
- tool_output:TO_type_system_rewrite-20260522T073012Z_m39727_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:7187-7335

## L1259 scope='C2.1.1.13.4' tags=Expr_Subscript,monadic-tail,Resume,boundary-helper
shape: Expr_Subscript monadic tail proofs should be in small adapters/helpers, not the Resume
pattern: Keep evaluator-tail reasoning (base/index error propagation, `get_Value`, `check_array_bounds`, `evaluate_subscript`, storage read) inside local adapter/helper theorems whose conclusions match the branch postcondition. In the Resume, only project the relevant ordinary/place IH and apply the adapter. Repeated exact case-tail rewrites and stack-position assumption plumbing in the Resume are brittle and have already failed.
works_when: Proving/removing cheats around `expr_subscript_ordinary_static_branch_sound_stmt`, `expr_subscript_place_as_ordinary_branch_sound_stmt`, and the Expr_Subscript Resume.
evidence:
- episode:E0688
- episode:E0691
- episode:E0695
- tool_output:TO_type_system_rewrite-20260522T073012Z_m39725_t001

## L1260 scope='C2.1.1.13.4' tags=Expr_Subscript,Resume,guarded-IH,adapter,proof-interface
shape: Expr_Subscript ordinary Resume has guarded index IH, not an unguarded standalone index IH
pattern: When installing ordinary/static Subscript adapters, inspect the live generated Resume context: the index-expression IH is guarded by a successful base evaluation (`!s'' tv1 t. eval_expr cx e s'' = (INL tv1,t) ==> ... eval_expr cx e' ...`). Adapter skeletons that expect an unguarded index IH will not match the caller. Make the adapter consume the guarded IH exactly or provide a tiny wrapper; do not discharge this mismatch with broad `simp`/`metis`.
works_when: C2.1.1.13.4 Expr_Subscript ordinary conjunct after splitting `well_typed_expr env (Subscript ...)` at the Resume boundary.
evidence:
- tool_output:TO_type_system_rewrite-20260522T073012Z_m39740_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m39748_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m39750_t001

## L1261 scope='C2.1.1.13.4' tags=Expr_Subscript,skeleton,tactic-timeout,simp,metis_tac
shape: Calling cheated adapter skeletons from a large mutual Resume times out with broad `simp[]`/`metis_tac`
pattern: For cleanup leaves that introduce cheated adapter skeletons, the caller should apply them with exact assumption selection or an interface that unifies directly. In a large mutual Resume, `metis_tac[skeleton]`, `irule skeleton >> simp[]`, and `rpt conj_tac >> first_assum ACCEPT_TAC` can still time out/fail before reaching the skeleton cheat. Treat this as adapter interface evidence, not a semantic proof obligation.
works_when: Wiring local boundary/adapter skeletons into `eval_all_type_sound_mutual` Resume branches with many IH assumptions.
evidence:
- tool_output:TO_type_system_rewrite-20260522T073012Z_m39747_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m39763_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m39772_t001

## L1262 scope='C2.1.1.13.4' tags=Expr_Subscript,adapter,qspecl_then,match_mp_tac,existential,skeleton
shape: Calling a local adapter theorem from a mutual Resume leaves `∃st. ...` because some universally quantified variables occur only in premises, not the conclusion.
pattern: When a skeleton/adapter theorem's conclusion matches the Resume goal but some parameters occur only in antecedents, do not rely on `irule`, `match_mp_tac`, `qexists`, or `HINT_EXISTS_TAC` to infer them. Explicitly specialize all adapter parameters with `qspecl_then [...] match_mp_tac` (or `mp_tac`) and then use targeted rewrites/assumptions to discharge the antecedent. This avoids bogus existential subgoals and type ambiguity.
works_when: Use for temporary adapter integration in large mutual soundness Resume proofs, especially when the adapter conclusion is exactly the final branch postcondition but premises carry evaluator/IH terms such as `st`, `res`, `st'`, or a base vtype.
evidence:
- episode:E0696
- tool_output:TO_type_system_rewrite-20260522T073012Z_m39819_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m39822_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m39827_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:7279-7289

## L1263 scope='C2.1.1.13.4.2' tags=Expr_Subscript,get_Value,subscript_type_ok,is_int_type,side-condition
shape: Ordinary static Subscript adapter, get_Value on index returns `INR y`; need `no_type_error_result (INR y)`.
pattern: For the get_Value-error subcase, use `int_expr_get_Value_INR_no_type_error` only after explicitly deriving `is_int_type (expr_type e')` from `subscript_type_ok (expr_type e) (expr_type e') v9`. Avoid trying to let broad `gvs[subscript_type_ok_def]` solve this inside an `impl_tac` over the specialized theorem while residual conjunctions are present.
works_when: Base expression and index expression both evaluated successfully, index has `expr_result_typed env e' x'`, `get_Value x' st2 = (INR y,st2)`, and the ordinary static assumption `subscript_type_ok (expr_type e) (expr_type e') v9` is in context.
evidence:
- episode:E0697
- tool_output:TO_type_system_rewrite-20260522T073012Z_m39875_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m39878_t001
- source:semantics/prop/vyperTypeSystemScript.sml:309-317

## L1264 scope='C2.1.1.13.4.2' tags=Expr_Subscript,subscript_type_ok,get_Value,is_int_type,boundary-helper
shape: Ordinary static Subscript adapter, get_Value on the index returns `INR y` and no-TypeError is needed.
pattern: Factor the integer-index side condition out of the main adapter. Prove/use `subscript_type_ok_index_is_int_stmt: subscript_type_ok base idx res ==> is_int_type idx`, then wrap `int_expr_get_Value_INR_no_type_error` in a branch-shaped helper such as `expr_subscript_index_get_Value_INR_no_type_error_stmt` taking `expr_result_typed env e' tv`, `subscript_type_ok (expr_type e) (expr_type e') v9`, and `get_Value tv st = (INR y,st')`. This avoids fragile direct antecedent construction in the large Subscript branch.
works_when: Base and index evaluations have both succeeded, the index result is `expr_result_typed env e' idx_tv`, and the ordinary static assumption `subscript_type_ok (expr_type e) (expr_type e') v9` is available.
evidence:
- episode:E0698
- tool_output:TO_type_system_rewrite-20260522T073012Z_m39905_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:7187-7208

## L1265 scope='C2.1.1.13.4.2' tags=HOL4,THEN1,Cases_on,subgoal-control,Expr_Subscript
shape: `Cases_on val_res >> simp_tac(srw_ss())[] >- branch1 >- branch2` in a large evaluator-tail proof leaves two full outer goals / `first subgoal not solved by second tactic`.
pattern: When a case split is followed by focused branches in a large monadic proof, parenthesize the split explicitly: `Cases_on `val_res` >- (simp_tac... >> branch1) >- (simp_tac... >> branch2)`. Do this before trying more helper instantiations; residual outer goals after `>-` often indicate tactic grouping/subgoal-count mismatch, not a missing lemma.
works_when: Use in local adapter proofs with nested `Cases_on` and `>>`/`>-` sequencing, especially when holbuild reports multiple failed input goals at the whole fragment rather than a single helper antecedent.
evidence:
- episode:E0698
- tool_output:TO_type_system_rewrite-20260522T073012Z_m39917_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m39908_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:7282-7300

## L1266 scope='C2.1.1.13.4.2' tags=Expr_Subscript,eval_expr,case-split,proof-interface,branch-helper
shape: Ordinary static Subscript adapter still has full outer `(case (INL base_tv,st1) of ... eval_expr e' ...)= (res,st') ==> ...` goal after splitting `idx_res`.
pattern: If explicit `val_res` branches and either `qspecl_then` or `drule_all` use of `expr_subscript_ordinary_tail_sound_stmt` still leave two full outer Subscript goals, stop optimizing the inner get_Value tail. The missing boundary is earlier: simplify or factor the base-success/index-success branch so the full evaluator equality is consumed/substituted immediately after the `eval_expr e'` split. A small branch helper taking the exact full equality plus ordinary/index IH facts is likely cleaner than more nested `>-` plumbing.
works_when: Use in `expr_subscript_ordinary_static_branch_sound_stmt` when holbuild reports residual outer Subscript implication goals at the `idx_res` split or before the tail helper, even though base and index typing facts are available.
evidence:
- episode:E0699
- tool_output:TO_type_system_rewrite-20260522T073012Z_m39926_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m39948_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m39950_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:7260-7307

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
