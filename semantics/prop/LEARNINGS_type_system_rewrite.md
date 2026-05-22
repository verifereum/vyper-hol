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

## L1168 scope='C2.1a' tags=TopLevelName,lookup_global,immutables,get_immutables,state
shape: TopLevelName declaration-NONE branch after `get_immutables cx src st = (INL imms,r)`
pattern: When closing missing-immutable contradictions after a successful `get_immutables`, first apply `get_immutables_success` and instantiate downstream env/immutable lemmas with the returned state `r`, not the original state variable. The success theorem rewrites the immutable map to `get_source_immutables src (case ALOOKUP r.immutables ... )` and gives the state equality needed for `env_consistent env cx r`.
works_when: Use in C2.1a no-declaration branch helpers where the live context has `get_immutables ... = (INL _, r)` and a missing `FLOOKUP` branch.
evidence:
- episode:E0593
- tool_output:TO_type_system_rewrite-20260521T174852Z_m35964_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:304-384

## L1169 scope='C2.1a' tags=TopLevelName,env_immutables_consistent,pair,metis-timeout
shape: Need `evaluate_type (get_tenv cx) ty = SOME imm_tv` and `value_has_type imm_tv imm_v` for immutable `FLOOKUP ... = SOME (imm_tv,imm_v)`
pattern: Pair-split immutable lookup payloads (`PairCases_on x'` / rename to `imm_tv,imm_v`) and explicitly specialize the `env_immutables_consistent_def` toplevel-vtypes clause. Avoid broad `metis_tac` over the unfolded invariant; use `current_immutables_well_typed` plus `imms_well_typed_get_source_immutables` for `value_has_type`.
works_when: Use for immutable success-only typing facts under `well_typed_expr env (TopLevelName ty (src,id))`, `env_consistent`, and `find_var_decl_by_num ... = NONE`.
evidence:
- episode:E0594
- tool_output:TO_type_system_rewrite-20260521T174852Z_m35981_t001
- tool_output:TO_type_system_rewrite-20260521T174852Z_m35980_t001

## L1170 scope='C2.1a.3' tags=TopLevelName,storage,bare_globals,env_consistent_toplevel_storage_static
shape: Need storage layout/evaluate-type witnesses for `TopLevelName ty (src,id)` with concrete `StorageVarDecl`
pattern: Split the interface: use `TopLevelName_nonbare_storage_decl_context` only under `FLOOKUP env.bare_globals (src,string_to_num id) = NONE` to obtain `typ = ty`, `IS_SOME evaluate_type`, and `IS_SOME lookup_var_slot_from_layout`; use `TopLevelName_storage_decl_type_eq` when only declaration type equality is needed. Do not try to infer layout witnesses in the bare-global branch.
works_when: Applies to C2.1a storage declaration branch helpers and any later TopLevelName storage consumers using `env_consistent_toplevel_storage_static`.
evidence:
- episode:E0596
- episode:E0598
- episode:E0599
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:386-423

## L1171 scope='C2.1a.5' tags=lookup_global,StorageVarDecl,expr_result_typed,read_storage_slot_success_type,evaluate_type_well_formed_type_value
shape: After unfolding `lookup_global_def` for a successful `StorageVarDecl` TopLevelName lookup, goals reduce to constructor-specific `value_has_type (Ctor ...) v` or direct ArrayRef typing.
pattern: Do not introduce existential witnesses after `gvs[expr_result_typed_def, expr_runtime_typed_def, toplevel_value_typed_def]` has simplified the goal into direct `value_has_type` obligations. In non-array read branches, prove a constructor-specific `well_formed_type_value (Ctor args)` from the matching `evaluate_type ... = SOME (Ctor args)` using `evaluate_type_well_formed_type_value`, then `drule_all read_storage_slot_success_type`. ArrayTV is direct by `toplevel_value_typed_def`.
works_when: Applies when the `lookup_global` storage branch is already constrained by successful `INL tvl` and concrete `StorageVarDecl` assumptions; use inside boundary helper, not consumers.
evidence:
- episode:E0603
- tool_output:TO_type_system_rewrite-20260521T174852Z_m36089_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:443-482

## L1173 scope='C2.1a.7.1' tags=is_immutable_decl,find_var_decl_by_num,duplicate-declarations,probe
shape: Need contradiction between immutable declaration existence and storage declaration lookup for same numeric id
pattern: `is_immutable_decl_def` scans the whole declaration list for an Immutable variable, while `find_var_decl_by_num_def` returns the first Storage/Transient/HashMap declaration for the numeric id. Unless a separate uniqueness invariant is available, duplicate declaration lists can likely make both predicates true; prove/check a concrete list pattern rather than assuming contradiction.
works_when: Use during C2.1a.7.1 or any later branch that tries to exclude duplicate storage/immutable declarations from scanner definitions alone.
evidence:
- tool_output:TO_type_system_rewrite-20260521T174852Z_m36129_t001
- tool_output:TO_type_system_rewrite-20260521T174852Z_m36130_t001
- tool_output:TO_type_system_rewrite-20260521T174852Z_m36141_t001

## L1174 scope='C2.1a.7' tags=TopLevelName,bare_globals,StorageVarDecl,invariant-repair,lookup_global
shape: Bare global typed as `Type ty` also appears as `find_var_decl_by_num = SOME (StorageVarDecl ...)`
pattern: For `lookup_global_TopLevelName_no_type_error`, the bare-global StorageVarDecl branch should be made contradictory by static consistency (`find_var_decl_by_num id ts = NONE` for bare globals), not handled by storage layout witnesses. E0607 rules out scanner-only contradiction from `is_immutable_decl`; E0608 rules out layout witnesses from old invariants. The repaired interface is `env_consistent_bare_global_find_NONE`, then a local impossible-branch lemma.
works_when: Use after the C2.1a.7.1 definition repair is in scope. Keep non-bare storage on `env_consistent_toplevel_storage_static`; use the new bare-global projection only for `FLOOKUP env.bare_globals = SOME _` branches.
evidence:
- episode:E0607
- episode:E0608
- tool_output:TO_type_system_rewrite-20260521T174852Z_m36184_t001

## L1175 scope='C2.1a.7.1' tags=HOL4,theorem-order,env_consistent_def,definition_repair
shape: Projection theorem over a definition just added/used in same script
pattern: When adding projection lemmas near definitions, place each theorem after all definitions it unfolds. In this edit, `env_consistent_bare_global_find_NONE` was inserted before `env_consistent_def`, causing a static `Value or constructor (env_consistent_def) has not been declared` error; move it after `Definition env_consistent_def`.
works_when: Applies to `vyperTypeSystemScript.sml` definition-repair components where env-context, scopes, immutables, and combined consistency definitions are declared sequentially.
evidence:
- tool_output:TO_type_system_rewrite-20260521T174852Z_m36191_t001
- tool_output:TO_type_system_rewrite-20260521T174852Z_m36192_t001

## L1176 scope='C2.1a.7' tags=TopLevelName,bare_globals,StorageVarDecl,env_consistent,boundary-lemma
shape: StorageVarDecl branch with FLOOKUP env.bare_globals (src,string_to_num id) = SOME bare
pattern: Close the branch by applying env_consistent_bare_global_find_NONE to derive get_module_code witness plus find_var_decl_by_num ... = NONE, then gvs/metis contradicts the StorageVarDecl assumption. Do not attempt lookup_var_slot_from_layout or rely on is_immutable_decl alone.
works_when: After the C2.1a.7.1 invariant repair is in scope and the branch has env_consistent plus bare_globals SOME and get_module_code/find_var_decl_by_num assumptions.
evidence:
- episode:E0609
- episode:E0610
- episode:E0611
- tool_output:TO_type_system_rewrite-20260521T174852Z_m36201_t001
- tool_output:TO_type_system_rewrite-20260521T174852Z_m36208_t001

## L1184 scope='C2.1.1.2' tags=IfExp,expr_result_typed,BoolT,evaluate_type,boundary_helper
shape: Need `toplevel_value_typed tv (BaseTV BoolT)` from condition result typing in Expr_IfExp
pattern: Use the local helper `expr_result_typed_BaseT_BoolT_value`: after unfolding `expr_result_typed_def` and `expr_runtime_typed_def`, finish with `gvs[evaluate_type_BaseT_BoolT]`. A single `rw[...]` including `evaluate_type_BaseT_BoolT` may leave the evaluate-type equality unspecialized; the post-unfold `gvs` step is the robust proof.
works_when: The context has `expr_result_typed env cond tv` and `expr_type cond = BaseT BoolT`, typically after the condition IH in `eval_all_type_sound_mutual[Expr_IfExp]`.
evidence:
- episode:E0624
- tool_output:TO_type_system_rewrite-20260521T174852Z_m36497_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:5770-5776

## L1185 scope='C2.1.1.2' tags=IfExp,switch_BoolV_post,branch_IH,boundary_helper,risk_mismatch
shape: Expr_IfExp selected branch after `switch_BoolV_post` leaves nested branch-IH continuation plumbing
pattern: Do not apply the branch IH directly inside the resume. Factor one-branch lifting (`ifexp_branch_from_cond_ih`) and a switch wrapper (`ifexp_switch_from_branch_ihs`) so their conclusions are the final IfExp postcondition. This avoids manual nested implication management produced by `switch_BoolV_post` continuations.
works_when: The generated mutual IH for e_true/e_false has an outer premise `eval_expr cx cond s0 = (INL tv0,t0)` and the final goal is the joint state/env/account/no-TypeError/result-typing invariant for `IfExp`.
evidence:
- episode:E0623
- tool_output:TO_type_system_rewrite-20260521T174852Z_m36491_t001
- tool_output:TO_type_system_rewrite-20260521T174852Z_m36489_t001

## L1186 scope='C2.1.1.2' tags=IfExp,switch_BoolV_post,qho_match_abbrev_tac,higher_order_predicate,boundary_helper
shape: Proving a wrapper over `switch_BoolV_post` where `irule switch_BoolV_post` cannot infer predicate `P`
pattern: Before applying `switch_BoolV_post`, abstract the desired postcondition with `qho_match_abbrev_tac `P res st'``. Then `irule switch_BoolV_post`, supply the switch equation with `goal_assum $ drule_at (Pat `switch_BoolV`)`, and in each continuation branch `qunabbrev_tac `P` >> BETA_TAC` before invoking the branch helper. Direct `irule`/`ho_match_mp_tac` on `switch_BoolV_post` can fail to infer or type-match the higher-order predicate.
works_when: The goal is a two-argument postcondition over `(res,st')` after `switch_BoolV`, and continuations can each prove that same postcondition from selected branch evaluation equations.
evidence:
- episode:E0626
- tool_output:TO_type_system_rewrite-20260521T174852Z_m36545_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:5821-5880

## L1187 scope='C2.1.1.3' tags=StructLit,exprs_runtime_typed,LIST_REL,OPT_MMAP,struct_has_type
shape: Proving successful `Expr_StructLit` result typing from `exprs_runtime_typed env (MAP SND kes) vs` and struct declaration facts
pattern: Use a local boundary lemma with conclusion matching the evaluator's constructed value: `expr_result_typed env (StructLit (StructT id) (src_id_opt,id) kes) (Value (StructV (ZIP (MAP FST args,vs))))`. In the proof, unfold `exprs_runtime_typed_def`, `expr_result_typed_def`, `expr_runtime_typed_def`, and `toplevel_value_typed_def`; witness `StructTV (ZIP (MAP FST args,tvs))`; use the StructT evaluate_type equation plus an OPT_MMAP-from-LIST_REL bridge to equate field type lists; finish with a same-names `struct_has_type` ZIP lemma.
works_when: The well-typed StructLit premise has `FLOOKUP env.type_defs (string_to_num id)=SOME (StructArgs args)`, `MAP FST kes = MAP FST args`, and `MAP (expr_type o SND) kes = MAP SND args`, and the expression-list IH supplies `exprs_runtime_typed env (MAP SND kes) vs`.
evidence:
- tool_output:TO_type_system_rewrite-20260521T174852Z_m36629_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:5984-6010

## L1188 scope='C2.1.1.3' tags=StructLit,monad,bind_def,error_propagation,qpat_x_assum
shape: StructLit error branch has `eval_exprs ... = (INR y,st1)` plus unsimplified monadic/case equation for the whole StructLit evaluator
pattern: Do not quote the `do` expression with `eval_exprs ... st` as the monadic argument. Select the live let/case equation as shown in the holbuild goal, move it to the goal, simplify with the exact `eval_exprs` equation using `asm_simp_tac(srw_ss())[Once bind_def, return_def, LET_THM]` (or after it has become a `case eval_exprs ...` equation), then use the resulting `res = INR y` and `st' = st1` to close by rewriting.
works_when: The branch came from `Cases_on exprs_res` where `exprs_res = INR y`; state/env/account and `no_type_error_result (INR y)` are already supplied by the expression-list IH.
evidence:
- tool_output:TO_type_system_rewrite-20260521T174852Z_m36631_t001
- tool_output:TO_type_system_rewrite-20260521T174852Z_m36645_t001
- episode:E0629

## L1189 scope='C2.1.1.4' tags=Expr_Subscript,IH-selection,guarded-IH,resume,replace_text
shape: Expr_Subscript resume raw goal has a guarded index IH followed by an unconditional base IH
pattern: In `Resume eval_all_type_sound_mutual[Expr_Subscript]`, do not apply `first_x_assum drule_all` after splitting the base evaluation. The first IH is guarded by a successful base-eval antecedent and is meant for the index expression `e'` only after the `INL tv1` base branch. Select/label the unconditional base IH explicitly for `e`; after the base-success case, instantiate the guarded index IH with the live `eval_expr cx e st = (INL tv1,st1)` fact.
works_when: After `rpt gen_tac >> strip_tac`, before or after one-step evaluator unfolding, the raw goal contains both IHs for the Subscript constructor: guarded index IH first and base IH second. Verify assumption order with holbuild before using positional selectors.
evidence:
- tool_output:TO_type_system_rewrite-20260521T174852Z_m36683_t001
- tool_output:TO_type_system_rewrite-20260521T174852Z_m36692_t001
- episode:E0631

## L1190 scope='C2.1.1.4' tags=Expr_Subscript,subscript_type_ok,get_Value,no-TypeError,resume
shape: Expr_Subscript direct `subscript_type_ok` branch, after base/index eval succeed and before splitting get_Value result
pattern: To prove `no_type_error_result value_res` for `get_Value x' st2` in the direct Expr_Subscript branch, unfold `expr_result_typed_def`/`expr_runtime_typed_def`, split `expr_type e`, simplify `subscript_type_ok_def` to obtain `is_int_type (expr_type e')`, then use `is_int_type_evaluate_type_not_None_Array` on the index expression's evaluated type and finish with `get_Value_no_type_error`. Do not try `drule_all` before exposing the `subscript_type_ok` cases.
works_when: The live assumptions include `subscript_type_ok (expr_type e) (expr_type e') result_ty`, `expr_result_typed env e' x'`, and `get_Value x' st2 = (value_res,st3)`. This covers the direct array/tuple expression-subscript branch, not the place/hashmap `subscript_vtype` branch.
evidence:
- tool_output:TO_type_system_rewrite-20260521T174852Z_m36744_t001
- tool_output:TO_type_system_rewrite-20260521T174852Z_m36746_t001
- episode:E0632

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

## L1195 scope='C2.1.1.4' tags=Expr_Subscript,well_typed_expr,type_place_expr,subscript_vtype,branch-split
shape: Expr_Subscript resume after `well_typed_expr_def` splits into direct value-subscript vs place-subscript disjuncts
pattern: Do not assume the base expression `e` is available as `well_typed_expr env e` in all `Subscript` branches. The direct branch has `well_typed_expr env e /\ subscript_type_ok (expr_type e) (expr_type e') v9`; the alternate branch has `type_place_expr env e = SOME vt /\ subscript_vtype vt (expr_type e') = SOME (Type v9)`. For the alternate branch, first use/prove a boundary lemma from `type_place_expr` to the needed base eval/result invariant, then reuse the guarded index IH and subscript_vtype helpers.
works_when: Applies inside `Resume eval_all_type_sound_mutual[Expr_Subscript]` after unfolding `well_typed_expr_def` and `evaluate_def`, splitting `eval_expr cx e st = (INL x,st1)`, and seeing a base IH guarded by `well_typed_expr env e`. If the live assumptions include `type_place_expr env e = SOME vt` but not `well_typed_expr env e`, switch to the place-subscript boundary path.
evidence:
- tool_output:TO_type_system_rewrite-20260521T174852Z_m37076_t001
- tool_output:TO_type_system_rewrite-20260521T174852Z_m37080_t001
- episode:E0636

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

## L1204 scope='C2.1.1.4.4' tags=AnnAssign,materialise,expr_result_typed,projection,tactic-timeout
shape: After ordinary expression projection, goal needs typedness or no-TypeError facts about `materialise cx tvl st = ...` from `expr_result_typed env e tvl`.
pattern: Use materialise boundary helpers instead of unfolding `expr_result_typed_def` in statement resumes. For error branches, `expr_result_typed_materialise_no_type_error` directly proves `err <> Error (TypeError msg)` from `well_typed_expr`, `expr_result_typed`, and the materialise equation. For success branches, the new helper `expr_result_typed_materialise_preserves_value_type` packages `expr_runtime_typed` + `materialise_preserves_value_type` to obtain `value_has_type tyv v`.
works_when: Applies in ordinary expression consumers after the strengthened expression IH has been projected with `well_typed_expr env e`; especially AnnAssign/Append/Assign/AugAssign materialise tails. Verify helper name/location before use because source is currently unverified after final edit.
evidence:
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:117
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:718
- tool_output:TO_type_system_rewrite-20260521T174852Z_m37331_t001
- episode:E0639

## L1205 scope='C2.1.1.4.4' tags=AnnAssign,monad,eval_stmt,boundary-helper,tactic-timeout
shape: A statement resume has a huge context and a pushed/expanded `(let tenv = ... in do ... od) st = (res,st')` AnnAssign evaluation equation.
pattern: Do not rewrite the expanded monadic equation inside the large resume. Prove a small statement-level equation helper over the original `eval_stmt cx (AnnAssign id typ e) st = (res,st')`, e.g. deriving `new_variable id tyv v st2 = (res,st')` or `res = INR exn /\ st' = st2`, then retain the original `eval_stmt` assumption and apply that helper. The let-shaped helper may prove in isolation but match poorly in the resume.
works_when: Use in AnnAssign after `eval_expr` and `materialise` have been case-split and the original `eval_stmt` equality can be kept in context. Avoid if the helper conclusion does not match the branch postcondition directly.
evidence:
- tool_output:TO_type_system_rewrite-20260521T174852Z_m37413_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:793
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:4277

## L1206 scope='C2.1.1.4.4' tags=AnnAssign,expression-IH,boundary-helper,tactic-timeout,statement-resume
shape: Statement resume under strengthened expression IH times out applying small branch helpers inside an expanded monadic evaluator equation.
pattern: Factor a whole statement-case helper that takes the ordinary expression IH projection and the original `eval_stmt` equation, performs the local evaluator unfolding/case split in a small theorem, and returns exactly the statement postcondition. Then the `Resume` proof should only extract static typing facts, prove the projection premise, and apply the helper.
works_when: Use for AnnAssign-like statement cases where the resume context includes the paired ordinary/place expression IH and broad branch-local simplification or `drule_all` matching times out. This pattern moved the build from AnnAssign to Append.
evidence:
- tool_output:TO_type_system_rewrite-20260521T174852Z_m37455_t001
- tool_output:TO_type_system_rewrite-20260521T174852Z_m37477_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:857
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:4370

## L1207 scope='C2.1.1.4.4' tags=statement-resume,expression-IH,case-split,tactic-timeout,Append,Assign,AugAssign
shape: Statement resume has a strengthened paired expression IH plus a target/base-target IH; after `Cases_on target_res` or `bt_res`, broad `gvs[no_type_error_result_def]` times out.
pattern: Do a manual result split with no simplifier: `Cases_on ...`; in the INL branch, expose only the postcondition case assumption with `qpat_x_assum `case INL _ of _ => _ | _ => _` mp_tac >> rewrite_tac[] >> strip_tac`, then rewrite the outer monadic pair/sum case with `pure_rewrite_tac[pairTheory.pair_case_def] >> BETA_TAC >> pure_rewrite_tac[sumTheory.sum_case_def] >> BETA_TAC`. In the INR branch, substitute `res`/`st'` from the outer equation, kill large IH assumptions, and prove state/accounts/no-TypeError from the already-projected target IH facts.
works_when: Use after base-target/target IH has already produced state/env/accounts/no-TypeError and runtime-shape facts, and the next failure is a timeout in `gvs`/`simp` immediately after a result case split. If multiple sub-resumes still need the same pattern, factor a whole-case helper instead.
evidence:
- tool_output:TO_type_system_rewrite-20260521T174852Z_m37539_t001
- tool_output:TO_type_system_rewrite-20260521T174852Z_m37545_t001
- tool_output:TO_type_system_rewrite-20260521T174852Z_m37553_t001
- episode:E0641

## L1208 scope='C2.1.1.4.4' tags=no_type_error_result,INR,TypeError,contradiction,tactic-timeout
shape: Goal is `no_type_error_result (INR y)` or its unfolded form, with context containing `!msg. y <> Error (TypeError msg)`.
pattern: Avoid assumption matching in a huge context. Either keep the goal unfolded as `!msg. INR y <> INR (Error (TypeError msg))` and reduce to the saved inequality, or after `rpt strip_tac` specialize the saved `!msg. y <> Error (TypeError msg)` to the current `msg` and derive contradiction from the equality. Do not rewrite the goal into the positive equality `y = Error (TypeError msg)`.
works_when: Applies to statement exception branches where no-TypeError came from a projected evaluator/target IH and was unfolded by `fs[no_type_error_result_def]`.
evidence:
- tool_output:TO_type_system_rewrite-20260521T174852Z_m37553_t001
- episode:E0641

## L1209 scope='C2.1.1.4.4' tags=Iterator_Range,expression-IH,tactic-timeout,get_Value,lift_sum,range
shape: Iterator_Range after strengthened expression IH has nested `eval_expr`/`get_Value`/`lift_sum (get_range_limits ...)` cases and paired ordinary/place IHs in context; broad `gvs` times out or explodes constructor cases.
pattern: Project ordinary expression postconditions immediately, discard unused place projections, and process monadic cases with targeted rewrites. For state-only functions use `drule get_Value_state` or `drule lift_sum_state` plus direct substitution instead of `imp_res_tac ... >> gvs[]`. For the range success tail, avoid case-splitting all value constructors; derive `v1 = IntV i` and `v2 = IntV j` from `expr_result_typed`, `get_Value` success, `is_int_type`, and `value_has_type`, or factor this into a `range_iterator_tail_sound` helper.
works_when: Applies to `Resume eval_all_type_sound_mutual[Iterator_Range]` or similar pure tail cases after the ordinary/place expression invariant refactor. Especially useful when holbuild shows timeouts at `Cases_on ... >> gvs[no_type_error_result_def]`, `get_Value_state >> gvs[]`, or broad value-constructor simplification.
evidence:
- tool_output:TO_type_system_rewrite-20260521T174852Z_m37603_t001
- tool_output:TO_type_system_rewrite-20260521T174852Z_m37613_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:5629
- episode:E0642

## L1211 scope='C2.1.1.5' tags=strengthened-IH,ordinary-projection,expr2,qpat_x_assum
shape: Second endpoint IH in strengthened expression invariant: `!env st res st'. ... ==> (well_typed_expr ... ==> ordinary) /\ place`
pattern: Do not rely on `drule_all` leaving an easily selectable `well_typed_expr _ e' ==> _` assumption. Explicitly instantiate the endpoint IH with `qspecl_then [env, st1, expr2_res, st3] mp_tac`, discharge env/state/evaluation premises, then move the `well_typed_expr env e' ==> _` projection and discharge it before splitting `expr2_res`.
works_when: The expression IH conclusion is the strengthened ordinary/place conjunction and only the ordinary endpoint projection is needed.
evidence:
- tool_output:TO_type_system_rewrite-20260521T174852Z_m37640_t001
- tool_output:TO_type_system_rewrite-20260521T174852Z_m37641_t001
- tool_output:TO_type_system_rewrite-20260521T174852Z_m37642_t001

## L1212 scope='C2.1.1.5' tags=Iterator_Range,range-tail-helper,lift_sum,get_range_limits,branch-closure
shape: After endpoint extraction in Iterator_Range: typed `IntV i1/i2` endpoints and `lift_sum (get_range_limits (IntV i1) (IntV i2)) st = (INL rl,st)` with goal `no_type_error_result (INL (GENLIST ...)) /\ EVERY ...`.
pattern: A local helper `iterator_range_tail_sound` near `range_values_well_typed` can package the range-success tail: from `value_has_type tv (IntV i1)`, `value_has_type tv (IntV i2)`, and the `lift_sum (get_range_limits ...)` success equation, derive both the no-TypeError conjunct and the `EVERY (value_has_type tv)` range-values conjunct. This avoids hand-managed `i1 <= i2` branches in the large mutual resume. The use site still needs a matched fact/application, not raw branch tactics.
works_when: Endpoint extraction has already rewritten both values to `IntV i1`/`IntV i2`, and `lift_sum_state` has substituted the state so the success equation has identical input/output state.
evidence:
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:4003-4020
- tool_output:TO_type_system_rewrite-20260521T174852Z_m37711_t001
- tool_output:TO_type_system_rewrite-20260521T174852Z_m37725_t001

## L1213 scope='C2.1.1.5.1' tags=Iterator_Range,whole-tail-helper,branch-leak,lift_sum,get_range_limits
shape: Local helper over `lift_sum (get_range_limits (IntV i1) (IntV i2)) st = (range_res,st_tail)` plus final tail equation
pattern: When a Resume branch split leaks helper implications into the sibling branch, move the split into a whole-tail helper. The helper should consume endpoint typedness, `evaluate_type`, the `lift_sum` equation, and the final tail pair equation, then return state equality, no-TypeError, and result typing. In the Resume, call the helper once after endpoint extraction instead of splitting on `range_res`.
works_when: Endpoint extraction has already yielded `v1 = IntV i1`, `v2 = IntV i2`, `value_has_type tyv (IntV i1/i2)`, and the tail is just `lift_sum (get_range_limits ...)` followed by return/raise.
evidence:
- tool_output:TO_type_system_rewrite-20260521T174852Z_m37798_t001
- episode:E0646
- tool_output:TO_type_system_rewrite-20260521T174852Z_m37803_t001

## L1214 scope='C2.1.1.5.1' tags=HOL4,drule,qexists_tac,helper-specialization
shape: Helper proof INL branch after `drule iterator_range_tail_sound` leaves goal `no_type_error_result ... /\ EVERY ...`, not an existential
pattern: If a reused helper returns exactly the no-TypeError/EVERY tail fact, do not continue with existential-witness tactics intended for the enclosing result-typing conjunct. Either specialize the helper directly with `qspecl_then [...] mp_tac ... >> simp[] >> strip_tac` and then separately witness result typing with `tyv`, or prove the tail fact in a named subgoal before assembling the helper's final conjunctions.
works_when: The local helper's final conclusion is a conjunction of state equality, no-TypeError, and a case expression; after `gvs[return_def,raise_def]`, the INL branch may split so the helper tail fact and existential result-typing fact must be handled at the correct subgoal.
evidence:
- tool_output:TO_type_system_rewrite-20260521T174852Z_m37804_t001

## L1216 scope='C2.1.1.5.2' tags=Iterator_Range,whole-tail-helper,resume-refactor,lift_sum
shape: After endpoint extraction to `IntV i1/i2`, live `lift_sum (get_range_limits (IntV i1) (IntV i2)) st3 = (range_res,st5)` plus final tail pair equation
pattern: In the Resume, call `iterator_range_tail_eval_sound` once after endpoint extraction and prove its final-tail antecedent by moving the live pair equation to the goal, case-splitting `range_res` inside the antecedent proof, and simplifying with `return_def`/`raise_def`. This avoids an outer range-res branch in the Resume.
works_when: Endpoint facts include `evaluate_type env.type_defs (expr_type e) = SOME tv`, `value_has_type tv (IntV i1)`, `value_has_type tv (IntV i2)`, and the final evaluator tail equation is still available as a case over `(range_res,st5)`.
evidence:
- tool_output:TO_type_system_rewrite-20260521T174852Z_m37874_t001
- episode:E0648

## L1217 scope='C2.1.1.5.2.2' tags=Iterator_Range,error-tail,get_Value,sum_case_def,helper-integration,performance
shape: Iterator_Range error-propagation branch with final tail equation `(case (INL tv1,st1) of ...) = (res,st')` or `(case (INR y,st1) of ...) = (res,st')` in the large mutual Resume
pattern: Do not simplify large Iterator_Range case tails in the Resume. First use a small control-flow helper (e.g. `iterator_range_first_get_value_error_eq`) to derive `res = INR y` and `st' = st1`, substitute with `SUBST_ALL_TAC`, then unpack the relevant expression IH and prove no-TypeError with a typed helper if needed. If applying `int_expr_get_Value_INR_no_type_error` via `irule`, the generated existential witness order is `e, env, st, st', tv, ty`.
works_when: The branch is pure error propagation before later endpoint/range computation; no state-changing tail beyond returning `(INR y,st1)` should occur. The first-expression IH is available as `well_typed_expr env e ==> ...`.
evidence:
- episode:E0651
- tool_output:TO_type_system_rewrite-20260521T174852Z_m37924_t001
- tool_output:TO_type_system_rewrite-20260521T174852Z_m37928_t001

## L1218 scope='C2.1.1' tags=mutual-Resume,control-flow,performance,case-tail,BaseTarget_Subscript,Iterator_Range
shape: Evaluator Resume branch with a final `(case (res,st) of ...) = (res',st')` tail and a broad `gvs`/`simp` timeout
pattern: Normalize evaluator control-flow tails only after isolating a single semantic branch. First derive/substitute the propagated `res`/`st'` equalities or use a tiny local control-flow lemma; then unpack IH frame/typing facts. Avoid `gvs[no_type_error_result_def, return_def]` or `AllCaseEqs()` across multiple live branches in the mutual proof.
works_when: The evaluator branch is pure sequencing/error propagation and the relevant IH already supplies frame preservation and no-TypeError facts for the sub-computation.
evidence:
- episode:E0652
- tool_output:TO_type_system_rewrite-20260521T174852Z_m38007_t001
- tool_output:TO_type_system_rewrite-20260521T174852Z_m38011_t001

## L1219 scope='C2.1.1' tags=mutual-Resume,proof-order,expression-projection,place-projection,Expr_Name,Expr_BareGlobalName
shape: Expression Resume branch where the goal is still `well_typed_expr env (Ctor ...) ==> ...` and a constructor lookup/soundness lemma is applied with `drule_all` too early
pattern: After evaluator simplification in expression Resume blocks, split ordinary expression and place-expression projections before applying constructor soundness lemmas. In the ordinary branch, `strip_tac` to move `well_typed_expr` into assumptions, then `drule_all` the lookup/soundness boundary lemma. Close the non-place projection separately by rewriting `well_typed_expr_def`/place-expression definitions. This fixed Expr_Name and is the intended shape for Expr_BareGlobalName.
works_when: The constructor is an ordinary expression with a vacuous/non-place `type_place_expr` projection, and the existing boundary lemma requires `well_typed_expr env (Ctor ...)` as a premise.
evidence:
- episode:E0654
- tool_output:TO_type_system_rewrite-20260521T174852Z_m38037_t001
- tool_output:TO_type_system_rewrite-20260521T174852Z_m38040_t001

## L1220 scope='C2.1.1.9' tags=TopLevelName,type_place_expr,lookup_global,place-projection,mutual-resume
shape: `Expr_TopLevelName` Resume after ordinary branch is solved, with remaining `type_place_expr env (TopLevelName ann nsid) = SOME vt ==> ...` projection.
pattern: Do not close the second expression projection for `TopLevelName` by vacuity. `type_place_expr` for `TopLevelName` is a real lookup into `env.toplevel_vtypes`; after `lookup_global_state` it still needs no-TypeError and success `place_expr_result_typed` reasoning. Prefer a local place-lookup boundary lemma over broad `gvs` in the mutual Resume.
works_when: Applies in `eval_all_type_sound_mutual[Expr_TopLevelName]` and similar name-like constructors that are also place expressions. Use after the ordinary `well_typed_expr` branch has been stripped and handled.
evidence:
- tool_output:TO_type_system_rewrite-20260521T174852Z_m38075_t001
- tool_output:TO_type_system_rewrite-20260521T174852Z_m38082_t001
- source:semantics/prop/vyperTypeSystemScript.sml:544-547

## L1221 scope='C2.1.1' tags=proof-order,well_typed_expr,drule_all,Resume,expression-projection
shape: Expression Resume goal still has `well_typed_expr env (Ctor ...) ==> ...` and a constructor lookup/soundness lemma is about to be applied.
pattern: For ordinary expression projection goals, first move/simplify the evaluator equation, enter the ordinary branch, and `strip_tac` the `well_typed_expr` antecedent before `drule_all` on constructor lookup/soundness lemmas. This fixed `BareGlobalName` and the ordinary part of `TopLevelName`.
works_when: Applies to constructor soundness lemmas whose first premise is `well_typed_expr env <same expression>` and the mutual theorem presents that premise as an implication antecedent.
evidence:
- episode:E0657
- tool_output:TO_type_system_rewrite-20260521T174852Z_m38068_t001
- tool_output:TO_type_system_rewrite-20260521T174852Z_m38074_t001

## L1222 scope='C2.1.1.9' tags=TopLevelName,type_place_expr,lookup_global,place-projection,boundary-lemma
shape: Need to prove `type_place_expr env (TopLevelName ann (src,id)) = SOME vt` plus `lookup_global ... = (res,st')` implies no-TypeError and `place_expr_result_typed`.
pattern: A clean boundary splits `vt`. For `Type ty`, if the name is not a bare global, use `env_consistent_toplevel_storage_static` plus `lookup_global_StorageVarDecl_no_type_error`, then unfold `lookup_global` only for INL success to prove `place_expr_result_typed (Type ty)`. If it is a bare global, derive `well_typed_expr env (TopLevelName ty (src,id))` from env-context consistency and reuse `lookup_global_TopLevelName_sound`, then bridge `expr_result_typed` to `place_expr_result_typed`. For `HashMapT kt vt`, use `env_consistent_toplevel_hashmap_static` and `lookup_global_HashMapVarDecl_returns_HashMapRef`.
works_when: Applies to `Expr_TopLevelName` place projection after `lookup_global_state` has normalized state equality and all standard mutual hypotheses (`env_consistent`, `state_well_typed`, `context_well_typed`, `accounts_well_typed`, `functions_well_typed`) are available.
evidence:
- tool_output:TO_type_system_rewrite-20260521T174852Z_m38093_t001
- tool_output:TO_type_system_rewrite-20260521T174852Z_m38096_t001
- tool_output:TO_type_system_rewrite-20260521T174852Z_m38133_t001

## L1224 scope='C2.1.1' tags=Resume,IfExp,joint-IH,ordinary-projection,place-projection,performance
shape: Expression Resume helper expects ordinary-only branch IH, but live mutual IH concludes `(well_typed_expr ... ==> ordinary) /\ (!vt. type_place_expr ... ==> place)`.
pattern: For expression Resume branches in the joint soundness theorem, helper lemmas that consume recursive expression IHs should either accept the joint IH shape directly or use a small adapter to extract the ordinary projection. Do not search for ordinary-only `well_typed_expr ... /\ ... ==> ...` assumptions when the live context contains joint ordinary/place projections.
works_when: Applies in `eval_all_type_sound_mutual` expression branches such as IfExp where branch dispatch helpers consume recursive expression IHs for subexpressions.
evidence:
- tool_output:TO_type_system_rewrite-20260521T174852Z_m38233_t001
- tool_output:TO_type_system_rewrite-20260521T174852Z_m38235_t001
- tool_output:TO_type_system_rewrite-20260521T174852Z_m38265_t001

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

## L1234 scope='C2.1.1.13' tags=Subscript,well_typed_expr,static_disjunct,Resume,proof_order
shape: `well_typed_expr env (Subscript v9 e e')` inside the mutual Resume exposes both ordinary-base and place-base static typing alternatives.
pattern: Split the Subscript static typing disjunction before evaluator-tail case analysis. The ordinary-base branch may use ordinary `expr_result_typed` facts and old array/value proof; the place-base branch must preserve `type_place_expr env e = SOME base_vt` and `subscript_vtype base_vt (expr_type e') = SOME ...`, use the base place IH, and then call a tail helper. A shared `FIRST [place helper; old ordinary tail]` after `get_Value` is the wrong abstraction.
works_when: Use in `Resume eval_all_type_sound_mutual[Expr_Subscript]` after unfolding `well_typed_expr_def` once. Especially important when HashMapRef/storage refs are possible in the place-base disjunct.
evidence:
- episode:E0677
- tool_output:TO_type_system_rewrite-20260522T073012Z_m38687_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m38683_t001

## L1235 scope='C2.1.1.13' tags=Subscript,place_projection,place_expr_result_typed,HashMapT,helper
shape: Separate Subscript place projection under `type_place_expr env (Subscript ...) = SOME result_vt` needs successful evaluator result typed as a place.
pattern: Do not derive the place projection from the expression-half helper alone. Add/use a helper whose success conclusion is `place_expr_result_typed env tv result_vt`; this is necessary for nested `HashMapT` place results, which are not ordinary expression results. Keep `evaluate_subscript_def`/nested hashmap unfolding inside that helper, not in the mutual Resume.
works_when: Use for C2.1.1.13.2/C2.1.1.13.4 and any later place-capable expression whose place projection can return HashMapT references.
evidence:
- tool_output:TO_type_system_rewrite-20260522T073012Z_m38687_t001
- episode:E0677
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:6759-6865

## L1236 scope='C2.1.1.13' tags=holbuild,branch-suffix,Resume,placeholder,cleanup
shape: A temporary Resume skeleton with branch-specific `>-` suffixes fails before proof search with `branch suffix without active branch`.
pattern: When normalizing a broken Resume only to create a safe editing placeholder, prefer the simplest single-flow skeleton (`rpt gen_tac >> strip_tac >> conj_tac >> rpt strip_tac >> cheat`) over a partially structured `reverse conj_tac >- (...) >> ...` placeholder. Save branch structure for the real proof component; holbuild instrumentation can reject suffixes in placeholder contexts.
works_when: Use only for source-cleanup placeholders under a planned component where local cheats are explicitly authorized; do not use as a proof strategy for terminal components.
evidence:
- episode:E0678
- tool_output:TO_type_system_rewrite-20260522T073012Z_m38698_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m38699_t001
- tool_output:TO_type_system_rewrite-20260522T073012Z_m38700_t001

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
