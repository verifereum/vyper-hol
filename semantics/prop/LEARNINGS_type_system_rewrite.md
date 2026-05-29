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

## L1307 scope='C4.3' tags=Extract32,type-builtin,boundary-helper,no-TypeError
shape: Main theorem branch has `well_typed_type_builtin_args Extract32 ...` and `evaluate_type_builtin ... Extract32 ... <> INR (TypeError msg)`.
pattern: After the Extract32 static repair, derive/use `extract32_result_base_ok bt` from `well_typed_type_builtin_args_def` and apply `evaluate_extract32_supported_no_type_error` in consumers. Avoid unfolding `evaluate_extract32_def` in the main theorem; destruct typed byte/int arguments only inside the local helper.
works_when: Applies in C4.3/C4.4 consumers after C4.3.1-C4.3.3 are in source. Runtime errors remain allowed; the helper excludes only TypeError.
evidence:
- episode:E0744
- episode:E0745
- tool_output:TO_type_system_rewrite-20260522T073012Z_m41360_t001
- source:semantics/prop/vyperTypeBuiltinsScript.sml:evaluate_extract32_supported_no_type_error

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

## L1365 scope='C4.4' tags=ABI,encoded-length,boundary-lemma,compacted
shape: ABI encode proof histories from old C4.4 subcomponents are stale unless C4.4 is rescheduled
pattern: If ABI/type-builtin work is later rescheduled, query dossier episodes for exact C4.4 evidence rather than relying on many stale per-branch learning cards. The stable strategic lesson is to prove encoded-length boundary lemmas directly (avoiding ABI `has_type` as the main invariant when Vyper integer widths are not ABI-valid) and consume those boundaries in builtin/type-builtin success proofs.
works_when: Only for future C4.4 ABI encode/type-builtin proof repair; not needed during C2.1 Len audit.
evidence:
- episode:E0752
- episode:E0755
- episode:E0766

## L1604 scope='global' tags=replace_text,source-cleanup,proof-probe
shape: Removing a temporary proof probe by replacing a short common tactic fragment.
pattern: Do not remove temporary probes with a generic `replace_text` fragment that may occur many times. Read the local source range and use line-anchored `edit_lines` or a unique block containing the theorem/line context; otherwise an identical tactic elsewhere can be edited while the probe remains.
works_when: Applies to cleanup of `FAIL_TAC`/probe fragments in large proof scripts with repeated `impl_tac >- simp[]` patterns.
evidence:
- tool_output:TO_type_system_rewrite-20260525T153549Z_m51705_t001

## L1626 scope='global' tags=HOL4-editing,replace_text,large-file,proof-safety
shape: Large HOL4 source contains repeated tactic fragments such as `conj_tac >- simp[]`; exact `replace_text` may hit an unintended occurrence.
pattern: For proof edits in large files, prefer `edit_lines` on a read/verified line range or include unique surrounding context in `replace_text`. Immediately inspect the edited hunk before building; accidental unrelated source changes can mask proof failures.
works_when: Any large `*Script.sml` file with repeated short tactic fragments.
evidence:
- tool_output:TO_type_system_rewrite-20260525T153549Z_m52293_t001

## L1729 scope='C2.6.4.1' tags=IntCall,defaults,finally,env_consistent,frame_package
shape: Default `finally` evaluation gives `eval_exprs ... (base_st with scopes := [FEMPTY]) = (res,framed_st)` and final state `framed_st with scopes := base_st.scopes`; need caller-frame package for final state.
pattern: Factor default-frame restoration into deterministic lemmas: `state_well_typed_restore_scopes` transfers `state_well_typed` from `framed_st` and the caller state's scopes; `env_consistent_restore_intcall_default_frame` combines caller `env_consistent env cx base_st` with defaults-env immutables preservation for `framed_st` to recover `env_consistent env cx (framed_st with scopes := base_st.scopes)`. Then the PLAN wrapper can be conjunction assembly plus existing bind-arguments success facts.
works_when: Use for C2.6.4.1 and similar default-argument `finally` helpers where `defaults_env` has empty var maps and the final state restores caller scopes after evaluating defaults under pushed IntCall context.
evidence:
- tool_output:TO_type_system_rewrite-20260525T153549Z_m56311_t001
- tool_output:TO_type_system_rewrite-20260525T153549Z_m56321_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:10308-10453

## L1730 scope='C2.6.4.1' tags=IntCall,defaults,frame_package,sum_case,proof_factoring
shape: Wrapper combines lower-level all-result frame helper with old success package; `case dflt_res` success branch has both frame and call_env facts.
pattern: When strengthening an existing no-TypeError/success package to an all-result frame package, first prove a lower-level all-result frame helper, then combine it with the existing package. Avoid `Cases_on res >> gvs[]` over giant IntCall assumptions; push each `case INL ...` assumption with `mp_tac`, rewrite only `sum_case_def`, strip, and assemble the existential explicitly.
works_when: Applies to IntCall/defaults helpers where one theorem supplies `state_well_typed/env_consistent/accounts/no_type_error_result` for all results and an older theorem supplies success-only `call_env`/scope facts.
evidence:
- episode:E1239
- tool_output:TO_type_system_rewrite-20260525T153549Z_m56348_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:13247-13373

## L1752 scope='C2.6.4.2.1' tags=IntCall,post-push,generated-IH,adapter,proof-interface
shape: Generated IntCall body IH must be consumed after concrete setup success
pattern: Factor the generated six-setup IH into a post-push adapter theorem before using tail/no-TypeError consumers. The adapter should have only setup equalities (`bind_arguments`, `evaluate_type`, lock equation) plus a `push_function ... = (INL cxf,pushed_st)` antecedent, and should return the quantified body soundness package. Large consumer theorems should call this boundary rather than specialize the generated IH directly.
works_when: Use when IntCall proof goals expose `state_well_typed st0'` or body soundness obligations from a six-setup generated IH while proving post-lock or general no-TypeError consumers.
evidence:
- episode:E1247
- tool_output:TO_type_system_rewrite-20260525T153549Z_m56741_t001
- tool_output:TO_type_system_rewrite-20260525T153549Z_m56771_t001

## L1755 scope='C2.6.4.2.1' tags=IntCall,post-push,boundary-lemma,no_type_error_result,conjunction-premise
shape: Large IntCall post-lock no-TypeError consumer with generated setup/body-IH premise and concrete `case INL ()` tail equation
pattern: For `intcall_default_success_general_post_lock_consumer_no_type_error`-style goals, introduce the theorem premise with `disch_then (fn th => map_every assume_tac (CONJUNCTS th))` so conjuncts are usable without splitting goals. In the success branch, instantiate `intcall_generated_body_ih_to_post_push_body_ih` explicitly with `qspecl_then`, normalize the concrete `case INL ()` tail equation by moving it to the goal and `simp[]`, then apply `intcall_default_success_post_lock_no_type_error_from_post_push_body_ih` and close its premise list with `asm_rewrite_tac[]`. Handle lock failure after simplifying `case INR e` and using `intcall_lock_no_type_error_result`.
works_when: Use after C2.6.4.2.1.2/C2.6.4.2.1.3 exist and a general IntCall no-TypeError consumer has the generated setup IH, bind/evaluate/lock equalities, and the post-lock monadic tail equation in assumptions.
evidence:
- episode:E1252
- tool_output:TO_type_system_rewrite-20260525T153549Z_m56946_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:12382-12409

## L1756 scope='C2.6.4.2.3' tags=IntCall,safe_cast,expr_result_typed,value_has_type,boundary-lemma
shape: Safe-cast success needs typed input to prove `expr_result_typed ... (Value crv)`
pattern: Do not try to derive `value_has_type ret_tv crv` from `safe_cast ret_tv rv = SOME crv` alone. State the IntCall safe-cast result boundary with an input `value_has_type ret_tv rv` premise, then use `safe_cast_preserves_well_typed`; unfold `expr_result_typed_def`, `expr_runtime_typed_def`, and `toplevel_value_typed_def` only in this local theorem and discharge the HashMapRef side condition using `well_typed_expr_not_hashmap_place`.
works_when: Applies to C2.6.4.2.3 and later C2.6.4.2.4 successful-Value branch, where the body IH/return_exception_typed should supply the returned runtime value typing.
evidence:
- tool_output:TO_type_system_rewrite-20260525T153549Z_m56966_t001
- tool_output:TO_type_system_rewrite-20260525T153549Z_m56974_t001
- plan:C2.6.4.2.3

## L1790 scope='C2.6.4.2.4.4.2.1' tags=IntCall,outer-INR,frame-restoration,return-polymorphic-boundary,no-fallthrough
shape: Outer `finally ... = (INR y,fin_st)` frame goal under `type_stmts env_body ret body = SOME env_after` and `ret = NoneT \/ stmts_no_fallthrough body`
pattern: Use a return-polymorphic frame boundary rather than a `NoneT`-specific helper. Split on `ret = NoneT`; delegate that case to the old `_apply` helper. In the no-fallthrough case, classify `finally` with `intcall_finally_try_handle_inr_body_cleanup_cases`; normal body success contradicts `cj 2 no_fallthrough_eval_no_success`, and body exception is handled by the body IH at the actual `ret` plus `intcall_cleanup_after_body_preserves_caller_frame`.
works_when: Applies to default internal-call outer-INR frame restoration where result typing/cast is irrelevant and the live theorem premise has arbitrary return type with a no-fallthrough disjunct. Failure sign: a subgoal asking for `type_stmts env_body NoneT body = SOME env_after` means the wrong boundary is being used.
evidence:
- tool_output:TO_type_system_rewrite-20260525T153549Z_m58336_t001
- tool_output:TO_type_system_rewrite-20260525T153549Z_m58346_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:11248-11326

## L1799 scope='C2.6.4.2.5.5' tags=IntCall,sum_case,proof_performance,lock_failure,branch-boundary
shape: Final IntCall continuation theorem failure branch has `lock_res = INR y` and an assumption `(case INR y of INL u => _ | INR e => _) = (res,st')` in a huge context
pattern: After splitting `lock_res`, do not simplify the `INR y` branch with broad `simp[]`/`gvs[]`. Push or select the exact case-equality assumption and use a minimal sum-case rewrite (e.g. `rewrite_tac[sum_case_def]`) to obtain the concrete `(INR y,lock_st) = (res,st')`/`res = INR y` and `st' = lock_st` facts before invoking `intcall_lock_attempt_sound_frame`.
works_when: Use in `intcall_successful_defaults_continuation_sound_general` and similar IntCall branch proofs where all phase assumptions are live and global simplification times out. Applies only after the success branch has been delegated to a boundary lemma and the remaining branch is `INR y`.
evidence:
- tool_output:TO_type_system_rewrite-20260525T153549Z_m58644_t001
- episode:E1296
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:15270-15276

## L1801 scope='C2.6.4.2.5.5' tags=IntCall,sum_case,PAIR_EQ,proof-performance,lock-failure
shape: Lock-failure branch has `(case INR y of ...) = (res,st')` or beta-expanded `(\e. (INR e,lock_st)) y = (res,st')` in a huge context
pattern: Avoid broad simplification. Select the exact equality, rewrite only `sum_case_def`, use `BETA_TAC` and `pure_rewrite_tac[PAIR_EQ]`, then substitute `st' = lock_st` and `res = INR y` explicitly. For the final `no_type_error_result (INR y)` goal, unfold/instantiate locally rather than invoking `gvs[]`.
works_when: Use in IntCall continuation or similar branch proofs after `Cases_on lock_res` leaves the `INR` failure branch and `intcall_lock_attempt_sound_frame` has supplied state/account/no-TypeError/env facts.
evidence:
- episode:E1297
- tool_output:TO_type_system_rewrite-20260525T153549Z_m58690_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:15270-15285

## L1804 scope='C2.6.4.2.5.6' tags=IntCall,branch-helper,generated-IH,boundary-lemma,risk-mismatch
shape: Full IntCall actual/default wrapper leaves generated-IH universal goals after direct continuation theorem application
pattern: If applying a continuation boundary theorem inside the main actual/default wrapper leaves generated-IH universal premises as live goals, the helper interface is too broad/late. Split the default-result cases into consumer-shaped branch helpers: one default-failure helper consuming stable frame facts before substitutions, and one default-success helper wrapping the continuation theorem with generated IHs as explicit leading premises. The authoritative wrapper should only derive the defaults package, case-split, and call the branch helpers.
works_when: Applies after `intcall_defaults_result_frame_package_from_generated_ih_general` is available and the wrapper goal has `dflt_res` cases. Do not use it to justify inlining lock/body/tail semantics; successful defaults should still delegate to `intcall_successful_defaults_continuation_sound_general`.
evidence:
- episode:E1300
- tool_output:TO_type_system_rewrite-20260525T153549Z_m58835_t001
- tool_output:TO_type_system_rewrite-20260525T153549Z_m58842_t001

## L1805 scope='C2.6.4.2' tags=IntCall,generated-IH,boundary-lemma,large-goal
shape: Large IntCall generated-IH/full-continuation goals exceed 4KB or leave body-IH premises
pattern: Keep IntCall proofs at phase-boundary level: package generated default/body IHs in small adapter lemmas, then compose defaults frame, lock-success/failure, post-push/body/cleanup/safe-cast, and actual/default wrapper helpers. Do not specialize generated IHs or unfold push/finally/cleanup/safe_cast inside the final consumer; if a helper leaves generated-IH premises in the main wrapper, add a consumer-shaped branch helper instead of selector tuning.
works_when: Applies throughout C2.6.4.2 IntCall soundness after actual/default evaluation or post-push body execution, especially when holbuild shows >4KB goals or repeated generated-IH premise discharge failures.
evidence:
- episode:E1243
- episode:E1285
- episode:E1291
- episode:E1300
- tool_output:TO_type_system_rewrite-20260525T153549Z_m58839_t001

## L1806 scope='C2.6.4.2.4' tags=IntCall,post-push,cleanup,safe_cast,expr_result_typed
shape: Post-push IntCall full soundness after finally/cleanup/safe-cast split
pattern: Use focused branch lemmas/classifiers for post-push soundness. Body IH supplies state/accounts/no-TypeError and return typing; cleanup lemmas restore caller state/env/accounts; safe-cast result typing should be factored into a tail lemma using value_has_type before lift_option_type/safe_cast simplification. Avoid broad env_consistent unfolding and avoid re-splitting cleanup in consumers.
works_when: Applies after `finally ... cleanup` has been split in `intcall_default_success_post_push_sound` or descendants; residuals mention caller frame facts and `lift_option_type (safe_cast rtv x)` equations.
evidence:
- episode:E1255
- episode:E1262
- episode:E1274
- episode:E1281
- tool_output:TO_type_system_rewrite-20260525T153549Z_m57786_t001

## L1807 scope='C2.6.4.2.5.6' tags=IntCall,default-failure,default-success,wrapper-interface
shape: Actual/default IntCall wrapper default-success/default-failure branch plumbing
pattern: For `intcall_actual_args_success_sound_from_generated_ih_general`, first derive the defaults frame package, then case-split on `dflt_res` and delegate to branch helpers. Default failure should use a tiny tail helper with `no_type_error_result_def` and `sum_case_def`; default success should wrap `intcall_successful_defaults_continuation_sound_general` with stable generated-IH/package premises. Do not continue qpat/first_assum variants after destructive case/substitution churn.
works_when: Applies in C2.6.4.2.5.6 and descendants when the wrapper has frame facts for `dflt_st` and an outer default-result case expression mapping `INR e` to `(INR e,dflt_st)` or `INL dflt_vs` to the continuation.
evidence:
- episode:E1299
- episode:E1300
- tool_output:TO_type_system_rewrite-20260525T153549Z_m58796_t001
- tool_output:TO_type_system_rewrite-20260525T153549Z_m58839_t001

## L1808 scope='C2.6.4.2.5.6' tags=IntCall,default-failure,no_type_error_result,helper-interface
shape: Default-failure helper for `(INR y,dflt_st) = (res,st')` leaves `no_type_error_result (INR y)`
pattern: A default-failure branch helper cannot prove `no_type_error_result (INR y)` for arbitrary `y`; include `no_type_error_result (INR y)` as a stable premise from the defaults package. Then normalize the pair equality and use/unfold that assumption with `no_type_error_result_def` instead of trying to prove the disequation from constructors alone.
works_when: Applies to IntCall/default-result helpers where an `INR` branch is returned unchanged and the final package includes `no_type_error_result res`. The premise is available from `intcall_defaults_result_frame_package_from_generated_ih_general`.
evidence:
- episode:E1302
- tool_output:TO_type_system_rewrite-20260525T153549Z_m58860_t002
- tool_output:TO_type_system_rewrite-20260525T153549Z_m58888_t001
- tool_output:TO_type_system_rewrite-20260525T153549Z_m58890_t001

## L1809 scope='C2.6.4.2.5.6' tags=IntCall,wrapper-refactor,premise-discharge,tactic-timeout,branch-helper
shape: Wrapper proof applies consumer-shaped branch helper but premise tail times out or leaves generated-IH goals
pattern: After deriving the defaults package in `intcall_actual_args_success_sound_from_generated_ih_general`, keep the main wrapper at branch-helper level. Do not use a broad `ORELSE` tail to discharge the success helper's many premises; it can time out and hide the missing premise. Discharge generated-IH premises first with explicit `qpat_assum` patterns, then scalar/package facts one-by-one, and preserve the full branch continuation equality for the final helper premise.
works_when: Applies to C2.6.4.2.5.6 wrapper refactors after `intcall_actual_args_success_default_success_branch` and `intcall_actual_args_success_default_failure_branch` are available. Especially useful when the success branch uses an abbreviation such as `lock_pair` to avoid destructing lock-result pairs.
evidence:
- episode:E1303
- tool_output:TO_type_system_rewrite-20260525T153549Z_m58918_t001
- plan:C2.6.4.2.5.6.4

## L1810 scope='C2.6.4.2.5.6.4.1' tags=IntCall,generated-IH,tactic-timeout,specialization,simp
shape: Generated body IH consumer theorem starts with `qhdtm_x_assum bool$! mp_tac >> simp[]` and times out on a large forall/implication goal
pattern: For IntCall generated-IH consumer proofs, specialize the generated forall assumption directly with `qspecl_then` before simplification. Moving the whole generated IH to the goal and running broad `simp[]` can time out after checkpoint eviction because the simplifier traverses the entire >4KB implication context. Discharge the instantiated antecedent with targeted rewrites/gvs on the smaller goal instead.
works_when: Applies to local IntCall helper theorems whose assumptions include a generated body/default IH and the proof only needs one concrete instantiation matching existing evaluator equalities.
evidence:
- tool_output:TO_type_system_rewrite-20260525T153549Z_m58968_t001
- plan:C2.6.4.2.5.6.4.1

## L1814 scope='C2.6.4.2.5.6.4.3' tags=IntCall,wrapper-refactor,pair-helper,lock-result,boundary-lemma
shape: Wrapper success branch needs to pass a lock acquisition result written as `lp` to a helper expecting separate `lock_res`/`lock_st` or `(FST lp,SND lp)` equality
pattern: When the final IntCall wrapper gets stuck proving `lock_call dflt_st = (FST lp,SND lp)` in a huge context, do not tune pair/abbrev tactics there. Add a local pair-shaped boundary helper around `intcall_actual_args_success_default_success_branch` that takes one `lock_pair` and internally bridges to the old separate lock result components; then the wrapper only discharges `lock_call dflt_st = lp` from the `Abbrev` assumption.
works_when: Applies in `intcall_actual_args_success_sound_from_generated_ih_general` after default success and before body/lock continuation. The semantic success-branch theorem must already be proved; the helper is only proof-interface glue, not evaluator unfolding.
evidence:
- episode:E1309
- tool_output:TO_type_system_rewrite-20260525T153549Z_m59057_t001
- tool_output:TO_type_system_rewrite-20260525T153549Z_m59060_t001

## L1815 scope='C2.6.4.2.5.6.4.3' tags=IntCall,pair-helper,boundary-lemma,branch-normal-form,env_body.current_src
shape: Pair helper around `intcall_actual_args_success_default_success_branch` leaves equality between branch expression using `env_body.current_src` and wrapper expression using `src_id_opt`
pattern: When wrapping the IntCall success-branch theorem with a pair-shaped helper, make the helper branch expression syntactically match the wrapper's pair-case form, then solve the helper-internal residual by targeted rewriting with `env_body.current_src = src_id_opt` and pair-case simplification. Do not expose the wrapper to `FST lp`/`SND lp`, and do not use broad metis over the huge generated-IH context.
works_when: Applies after `lock_pair` has been `PairCases_on` in the local helper and the old separate-lock theorem has been applied. The residual goal is a continuation equality, not a semantic obligation.
evidence:
- episode:E1310
- tool_output:TO_type_system_rewrite-20260525T153549Z_m59103_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:15671-16006

## L1818 scope='C2.6.4.2.5.6.4.3' tags=IntCall,generated-IH,boundary-lemma,post_push,timeout
shape: Local IntCall helper theorem times out on `qhdtm_x_assum `bool$!` mp_tac >> simp[]` over a massive generated evaluator IH
pattern: When a source-order IntCall bridge theorem such as `intcall_generated_body_post_push_ih` needs a body-IH continuation, do not simplify the raw generated IH. Use the already-proved consumer bridge (`intcall_generated_body_ih_live_consumer_premise`) to obtain the continuation, then instantiate the much smaller continuation with concrete bind/evaluate-ret/lock/push facts and solve only small operational rewrite subgoals.
works_when: Applies in the local IntCall successful-defaults/live-wrapper cluster after recursion/module/function/default-evaluation premises are already assumptions and the goal is a post-push body soundness conclusion. It does not authorize unfolding evaluator internals or changing theorem statements.
evidence:
- tool_output:TO_type_system_rewrite-20260525T153549Z_m59289_t001
- tool_output:TO_type_system_rewrite-20260525T153549Z_m59300_t001
- episode:E1307
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:14587-14700

## L1820 scope='C2.6.4.2.5.6.4.3' tags=IntCall,generated-IH,boundary-lemma,post_push,timeout
shape: Local post-push theorem needs body soundness after defaults/bind/return/lock/push, but raw generated-IH simplification times out
pattern: Derive a small continuation from `intcall_generated_body_ih_live_consumer_premise` first, then instantiate that continuation with `call_env`, `dflt_st`, `dflt_st`, `lock_st`, pushed context, and pushed state. This avoids simplifying the raw generated evaluator IH and keeps operational subgoals limited to `lift_option_type_def`, `evaluate_type_def`, `return_def`, and `push_function_def`.
works_when: Applies in the IntCall successful-defaults/post-push cluster once recursion/module/function/args/defaults result facts are already assumptions and the desired conclusion is the generated body soundness package for `fn_body`.
evidence:
- tool_output:TO_type_system_rewrite-20260525T153549Z_m59317_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:14674-14718
- episode:E1314

## L1824 scope='C2.6.4.2.5.6.4.3' tags=IntCall,default-failure,boundary-lemma,large-context,no_type_error_result
shape: Wrapper default-failure branch has unsplit `dflt_res`, frame facts, and full `(case dflt_res of ...)=...` equality, but post-split `no_type_error_result (INR y)` is unselectable in >4KB context
pattern: Derive a pre-split case-valued boundary fact before `Cases_on dflt_res`: consume `no_type_error_result dflt_res` plus the full unsimplified default-result equality and conclude `case dflt_res of INL _ => T | INR _ => <final wrapper tail>`. Then the `INR` branch closes by simplifying the labelled case fact, not by selecting `no_type_error_result (INR y)` from the wrapper context.
works_when: Use in `intcall_actual_args_success_sound_from_generated_ih_general` after `intcall_defaults_result_frame_package_from_generated_ih_general` supplies frame facts and `no_type_error_result dflt_res`, before splitting `dflt_res`. Helper must treat the success branch opaquely and prove nothing in the `INL` case.
evidence:
- episode:E1315
- tool_output:TO_type_system_rewrite-20260525T153549Z_m59523_t001
- tool_output:TO_type_system_rewrite-20260525T153549Z_m59521_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:15535-16125

## L1825 scope='C2.6.4.2.5.6.4.3' tags=IntCall,default-failure,boundary-lemma,large-context,no_type_error_result,sum_case
shape: Pre-split `failure_tail` fact for `case dflt_res of INL _ => T | INR _ => <wrapper tail>` in large IntCall generated-IH context
pattern: A pre-split case-valued helper can close the IntCall default-failure tail, but apply it with exact premise discharge and keep final use narrow: instantiate the opaque success-tail lambda explicitly, discharge frame/no-TypeError/full-case-equality premises with targeted assumptions, then in the `INR` branch use `asm "failure_tail" mp_tac >> rewrite_tac[sumTheory.sum_case_def] >> disch_then ACCEPT_TAC`. Avoid broad `simp` on the labelled fact in the huge wrapper context.
works_when: Use after `intcall_defaults_result_frame_package_from_generated_ih_general` has supplied `state_well_typed dflt_st`, `env_consistent env cx dflt_st`, `accounts_well_typed dflt_st.accounts`, `no_type_error_result dflt_res`, and the full unsplit default-result equality; the success branch should be treated opaquely.
evidence:
- episode:E1316
- tool_output:TO_type_system_rewrite-20260525T153549Z_m59551_t001
- tool_output:TO_type_system_rewrite-20260525T153549Z_m59549_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:15627-15648
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:16056-16159

## L1826 scope='C2.6.4.2.5.6.4.3' tags=IntCall,compatibility-wrapper,joint-theorem,MATCH_MP_TAC,projection
shape: Downstream no-TypeError wrapper application fails with `MATCH_MP_TAC` no-match after joint soundness theorem passes
pattern: When a stronger joint theorem has been refactored and now builds, stale no-TypeError helper/call sites may fail by theorem-shape mismatch rather than by a proof subgoal. Prefer repairing the no-TypeError wrapper as a projection from the joint theorem (`..._sound_from_generated_ih_general`) instead of duplicating IntCall evaluator/default-failure reasoning or continuing premise plumbing at the call site.
works_when: Applies after focused build advances past the joint wrapper theorem and fails at `MATCH_MP_TAC ... intcall_actual_args_success_no_type_error_from_generated_ih_general` in `eval_all_type_sound_mutual[Expr_Call_IntCall]`.
evidence:
- episode:E1316
- tool_output:TO_type_system_rewrite-20260525T153549Z_m59551_t001
- tool_output:TO_type_system_rewrite-20260525T153549Z_m59552_t002
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:16499-16503

## L1827 scope='C2.6.4.2.5.6.4.3' tags=IntCall,call-site,evaluator-shape,MATCH_MP_TAC,premise-discharge
shape: Downstream `Expr_Call_IntCall` wrapper has a whole `(case get_scopes args_st of ... finally ... ) = (res,st') ==> ...` goal while helper expects exposed `finally ... = (dflt_res,dflt_st)` and package assumptions
pattern: Before applying IntCall actual/default helper theorems at a downstream evaluator call site, normalize the evaluator tail to the helper interface: keep the successful `args_res` context, unpack `callable_body_typing_from_env_consistent` explicitly, simplify `get_scopes_def`/`return_def`, split `get_scopes`, split the default `finally` result, then apply the helper. Direct `MATCH_MP_TAC` on the unsplit case expression fails by shape mismatch.
works_when: Use in `eval_all_type_sound_mutual[Expr_Call_IntCall]` after actual args have evaluated successfully and callable-body typing facts are available. After the helper matches, discharge premises explicitly; do not rely on generic `first_assum`.
evidence:
- tool_output:TO_type_system_rewrite-20260525T153549Z_m59559_t001
- tool_output:TO_type_system_rewrite-20260525T153549Z_m59580_t001
- tool_output:TO_type_system_rewrite-20260525T153549Z_m59594_t001

## L1828 scope='C2.6.4.2.5.6.4.3' tags=IntCall,downstream-wrapper,premise-discharge,sig-param-types,generated-IH
shape: Downstream `Expr_Call_IntCall` no-TypeError wrapper after helper matching still has stale `sig.param_types`/`sig.num_defaults` expressions in the evaluator tail
pattern: Before applying `intcall_actual_args_success_no_type_error_from_generated_ih_general` in the downstream wrapper, derive `sig.param_types = MAP SND x''2 /\ sig.num_defaults = LENGTH x''3` from `fn_sigs_consistent_FLOOKUP` after `PairCases_on x''` and callable-body unpacking. This matches the successful local helper proof shape and prevents the tail from retaining `sig` fields where the helper expects tuple fields.
works_when: Use in `eval_all_type_sound_mutual[Expr_Call_IntCall]` after successful lookup/function typing, `PairCases_on x''`, and before `simp[get_scopes_def, return_def]`/default-result splitting. It does not replace explicit premise discharge after the helper application.
evidence:
- tool_output:TO_type_system_rewrite-20260525T153549Z_m59619_t001
- tool_output:TO_type_system_rewrite-20260525T153549Z_m59621_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:16362-16376
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:16502-16519

## L1829 scope='C2.6.4.2.5.6.4.3' tags=IntCall,joint-wrapper,projection,no-TypeError,premise-discharge
shape: Trying to prove a joint Resume goal with a helper whose conclusion is only `no_type_error_result res`
pattern: Before replacing a joint soundness Resume tail with an existing no-TypeError helper, compare conclusions: `MATCH_MP_TAC` will fail if the live goal also requires state/env/account preservation and result typing. Use the no-TypeError helper only as a template for evaluator normalization, or wrap/strengthen it with a joint compatibility theorem.
works_when: Applies in `eval_all_type_sound_mutual[Expr_Call_IntCall]` after the place-expression conjunct is discharged and the remaining expression branch conclusion is the joint preservation/no-TypeError/result-typed invariant.
evidence:
- tool_output:TO_type_system_rewrite-20260525T153549Z_m59641_t001
- episode:E1318
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:16162-16262

## L1830 scope='C2.6.4.2.5.6.4.3' tags=IntCall,normalized-tail,generated-IH,FIRST_ASSUM,helper-extraction
shape: Normalized downstream IntCall evaluator tail after helper application still fails at broad `FIRST_ASSUM` premise discharge
pattern: Once evaluator-tail normalization exposes the helper shape, do not use `rpt conj_tac >> first_assum ACCEPT_TAC` in the generated-IH context. Either discharge each premise with stable shape-specific tactics from the instrumented goal or extract a local compatibility helper matching the normalized tail; broad assumption search remains brittle even after the old `MATCH_MP_TAC No match` is fixed.
works_when: Use after assumptions include `default_ih`, `body_ih`, lift/get_module/lookup/type_check/eval facts, callable-body package facts, and the conclusion is the full normalized `case get_scopes ... finally ... = (res,st') ==> joint tail`.
evidence:
- tool_output:TO_type_system_rewrite-20260525T153549Z_m59653_t001
- tool_output:TO_type_system_rewrite-20260525T153549Z_m59663_t001
- episode:E1318

## L1831 scope='C2.6.4.2.5.6.4.3' tags=IntCall,joint-helper,downstream-wrapper,implication,premise-discharge
shape: Downstream Expr_Call_IntCall branch applies a joint helper to a normalized evaluator-tail implication
pattern: When replacing a no-TypeError-only downstream helper with the stronger joint `intcall_actual_args_success_sound_from_generated_ih_general`, first expose the evaluator-tail equality by `strip_tac`; otherwise the helper is applied while the goal is still the whole implication. After `strip_tac`, use explicit premise discharge or a compatibility helper, not broad `first_assum`.
works_when: Use after `get_scopes`/`finally` have been split in `eval_all_type_sound_mutual[Expr_Call_IntCall]` and the branch conclusion has shape `(case ...)= (res,st') ==> state_well_typed st' /\ env_consistent ... /\ no_type_error_result res /\ ...`.
evidence:
- tool_output:TO_type_system_rewrite-20260525T153549Z_m59680_t001
- tool_output:TO_type_system_rewrite-20260525T153549Z_m59683_t001
- episode:E1319

## L1832 scope='C2.6.4.2.5.6.4.3' tags=IntCall,generated-IH,qpat_assum,assumption-selection,large-context
shape: Initial downstream Expr_Call_IntCall branch has labelled `default_ih`/`body_ih` plus concrete `lift_option_type ... "IntCall ..." r = ...` assumptions
pattern: In a labelled generated-IH context, wildcard `qpat_assum` patterns for common evaluator facts can fail before the intended proof point because the generated IHs contain many similar subterms. Use exact message/state patterns (e.g. the literal `"IntCall get_module_code"` and state `r`) or package the extraction in a helper; a probe after the selection not being reached is evidence the selection itself is suspect.
works_when: Use after `actual_ih` has been consumed and the proof is about the successful IntCall actual-args branch with labelled `default_ih`/`body_ih` still in assumptions. This does not solve later joint-helper premises; it only stabilizes early branch normalization.
evidence:
- tool_output:TO_type_system_rewrite-20260525T153549Z_m59710_t001
- tool_output:TO_type_system_rewrite-20260525T153549Z_m59711_t001
- episode:E1320
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:16485-16488

## L1833 scope='C2.6.4.2.5.6.4.3' tags=IntCall,downstream-wrapper,probe-localization,generated-IH,get_scopes,qpat_assum
shape: Downstream Expr_Call_IntCall branch reaches probes after exact lift-option extraction, pair decomposition, callable-body unpack, sig-field derivation, and get_scopes TOP_CASE
pattern: When localizing the downstream IntCall Resume branch, exact message/state lift-option extraction with `mp_tac (MATCH_MP (iffLR lift_option_type_INL_eq) th) >> strip_tac` can advance through the early normalization steps. If a failure remains after `get_scopes` TOP_CASE, do not blame the initial lift-option qpat steps; inspect/factor the `scope_res`/finally/default branch or extract a compatibility helper.
works_when: Use in `eval_all_type_sound_mutual[Expr_Call_IntCall]` after actual args evaluate to `INL` and labelled `default_ih`/`body_ih` remain in assumptions. The source currently has a probe after `BasicProvers.TOP_CASE_TAC`; remove it before continuing.
evidence:
- tool_output:TO_type_system_rewrite-20260525T153549Z_m59727_t001
- tool_output:TO_type_system_rewrite-20260525T153549Z_m59732_t001
- tool_output:TO_type_system_rewrite-20260525T153549Z_m59739_t001
- tool_output:TO_type_system_rewrite-20260525T153549Z_m59742_t001
- tool_output:TO_type_system_rewrite-20260525T153549Z_m59745_t001
- episode:E1321
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:16485-16507

## L1834 scope='C2.6.4.2.5.6.4.3' tags=IntCall,downstream-wrapper,boundary-lemma,get_scopes,finally,generated-IH,helper-extraction
shape: Downstream Expr_Call_IntCall branch reaches after `get_scopes` TOP_CASE with a whole `(case get_scopes args_st of ... finally ... ) = (res,st') ==> joint tail` goal in a >4KB generated-IH context
pattern: At this point, stop inline qpat/FIRST_ASSUM premise plumbing and extract a local compatibility helper for the downstream evaluator-tail branch. The helper should package `qmatch_asmsub_rename_tac`/`scope_res` splitting, default `finally` splitting, and the application of `intcall_actual_args_success_sound_from_generated_ih_general`, presenting the Resume proof with a small conclusion matching the joint tail. A reached probe immediately after get_scopes TOP_CASE is evidence the earlier lift-option/callable-body/sig-field steps are not the blocker.
works_when: Use in `eval_all_type_sound_mutual[Expr_Call_IntCall]` after successful actual-args evaluation, exact lift-option extraction, `PairCases_on x''`, callable-body unpack, sig-field derivation, and `simp[get_scopes_def, return_def] >> BasicProvers.TOP_CASE_TAC` have succeeded; labelled `default_ih`/`body_ih` still pollute the context.
evidence:
- tool_output:TO_type_system_rewrite-20260525T153549Z_m59775_t001
- tool_output:TO_type_system_rewrite-20260525T153549Z_m59777_t001
- episode:E1322
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:16485-16556

## L1835 scope='C2.6.4.2.5.6.4.3' tags=IntCall,downstream-wrapper,generated-IH,probe,boundary-lemma,FIRST_ASSUM
shape: After removing `probe_after_get_scopes_top_case_2`, downstream Expr_Call_IntCall still fails with FIRST_ASSUM-origin in the whole get_scopes/finally tail despite local `simp`/probe changes
pattern: If the downstream IntCall Resume branch still reports FIRST_ASSUM-origin after the old get_scopes probe is removed, do not tune `Cases_on scope_res` or switch `gvs`/`simp` hoping to expose a smaller premise. This confirms the need for a use-site compatibility helper that packages the whole evaluator tail and applies the joint IntCall helper in a small proof context.
works_when: Use after exact lift-option extraction, pair decomposition, callable-body unpack, sig-field derivation, and get_scopes TOP_CASE are known to succeed, and the remaining goal is the large whole evaluator-tail implication. Remove any temporary FAIL_TAC before applying this pattern.
evidence:
- episode:E1323
- tool_output:TO_type_system_rewrite-20260525T153549Z_m59787_t001
- tool_output:TO_type_system_rewrite-20260525T153549Z_m59801_t001
- tool_output:TO_type_system_rewrite-20260525T153549Z_m59804_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:16507-16556

## L1836 scope='C2.6.4.2.5.6.4.3' tags=IntCall,downstream-wrapper,premise-discharge,lift_option_type,type_check,large-context
shape: Expr_Call_IntCall downstream branch after applying `intcall_actual_args_success_sound_from_generated_ih_general` fails on explicit lift_option/type_check helper premises in a >4KB generated-IH context
pattern: For the first two lift_option premises, avoid qpat/FIRST_ASSUM selection entirely; after successful branch normalization has rewritten the options to `SOME ...`, `simp[lift_option_type_def, return_def]` closes them. For the args-length/type_check premise, first push the existing checked length assumption (`type_check (LENGTH es <= LENGTH x''2 /\ LENGTH x''2 <= LENGTH es + LENGTH x''3) ... = (INL (),r)`) through `simp[type_check_def, assert_def, return_def, raise_def]` to obtain the arithmetic fact, then `simp[type_check_def, assert_def, return_def]` closes the helper premise with `tc_ok`.
works_when: Use only after `PairCases_on x'' >> gvs[]`, `sig.param_types = MAP SND x''2`, `sig.num_defaults = LENGTH x''3`, `get_scopes` normalization, and direct application of `intcall_actual_args_success_sound_from_generated_ih_general`; it does not solve later MAP/default/result equality premises.
evidence:
- tool_output:TO_type_system_rewrite-20260525T153549Z_m59821_t001
- tool_output:TO_type_system_rewrite-20260525T153549Z_m59828_t001
- episode:E1324
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:16518-16523

## L1839 scope='C2.6.4.2.5.6.4.3' tags=IntCall,expr_type,fn_sigs_consistent,premise-discharge,boolean-equivalence
shape: After `intcall_actual_args_success_sound_from_generated_ih_general`, tail needs `expr_type (Call sig.ret_ty ...) = x''4` and `∀n b. ... ==> ... (b <=> T)`
pattern: Prove the call `expr_type` premise by deriving `fn_sigs_consistent env.fn_sigs cx` from `env_consistent`, applying `fn_sigs_consistent_FLOOKUP`, and then simplifying with `expr_type_def`; `simp[expr_type_def]` alone leaves the return-type equality. For the `var_assignable` premise, exact `ACCEPT_TAC` may fail because the helper expects `(b <=> T)` while the callable-body package gives `b = T`; use `rpt strip_tac`, specialize the forall on `n` and `b`, then `gvs[]`.
works_when: In `eval_all_type_sound_mutual[Expr_Call_IntCall]` after successful actual-args/default-tail normalization and direct application of `intcall_actual_args_success_sound_from_generated_ih_general`, with assumptions containing `FLOOKUP env.fn_sigs ... = SOME sig`, `lookup_callable_function ... = SOME (...,x''4,...)`, callable-body package facts, and env consistency.
evidence:
- episode:E1327
- tool_output:TO_type_system_rewrite-20260525T153549Z_m59883_t001
- tool_output:TO_type_system_rewrite-20260525T153549Z_m59884_t001
- tool_output:TO_type_system_rewrite-20260525T153549Z_m59888_t001
- tool_output:TO_type_system_rewrite-20260525T153549Z_m59889_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:16539-16555

## L1840 scope='C2.6.4.3' tags=IntCall,generated-IH,boundary-lemma,joint-soundness
shape: A no-TypeError helper over generated IntCall IHs exists, but the consumer Resume goal needs full joint preservation/result-typing.
pattern: When upgrading an IntCall generated-IH helper from `no_type_error_result res` to full joint soundness, keep the same generated-IH selectors/evaluator split but make the helper conclusion match the Resume first conjunct exactly. Prefix and actual-args failure branches can reuse the old proof shape; actual-args success should delegate to the already-proved joint phase helper rather than exposing every intermediate at the Resume call site.
works_when: Use inside `vyperTypeStmtSoundnessScript.sml` for `Expr_Call_IntCall`, after the phase helpers under C2.6.4.1/C2.6.4.2 and the default-failure-tail repair are build-clean.
evidence:
- tool_output:TO_type_system_rewrite-20260525T153549Z_m59917_t001
- tool_output:TO_type_system_rewrite-20260525T153549Z_m59919_t001
- episode:E1327

## L1841 scope='C2.6.4.4' tags=IntCall,MATCH_MP_TAC,Q.SPECL,generated-IH,proof-integration
shape: Applying a boundary helper in a Resume leaves an existential package for variables that occur only in helper antecedents.
pattern: When integrating `intcall_expr_sound_from_generated_ih` into `Expr_Call_IntCall`, do not rely on bare `MATCH_MP_TAC`: explicitly specialize the helper with the live variables (`cx`, `env`, `st`, `res`, `st'`, `loc`, `src_id_opt`, `fn`, `es`, `extra`) before `MATCH_MP_TAC`. Otherwise HOL may leave a large `?st`/premise-package subgoal instead of matching the live assumptions.
works_when: Use in `vyperTypeStmtSoundnessScript.sml` C2.6.4.4 after the three generated IH assumptions have been labelled and the goal is the first conjunct of the IntCall Resume.
evidence:
- tool_output:TO_type_system_rewrite-20260525T153549Z_m59947_t001
- tool_output:TO_type_system_rewrite-20260525T153549Z_m59949_t001
- episode:E1331

## L1842 scope='C2.6.4.4' tags=IntCall,type_place_expr,strip_tac,generated-IH
shape: Place-expression impossibility branch has many generated-IH antecedents before the actual `type_place_expr ... = SOME _` premise.
pattern: In the second conjunct of `Resume eval_all_type_sound_mutual[Expr_Call_IntCall]`, open with `rpt gen_tac >> strip_tac`, not `rpt strip_tac`, before using `type_place_expr_Call_IntCall_NONE`. This preserves generated-IH assumptions as single antecedents and avoids splitting them into huge irrelevant goals.
works_when: Use for the IntCall place-expression impossibility branch where the only real contradiction is `type_place_expr _ (Call _ (IntCall _) _ _) = SOME _` versus `type_place_expr_Call_IntCall_NONE`.
evidence:
- tool_output:TO_type_system_rewrite-20260525T153549Z_m59939_t001
- episode:E1331

## L1843 scope='C2.7' tags=audit,cheat,holbuild,theory-build,proof-integrity
shape: A focused HOL theory target builds successfully while C2.7 remains active.
pattern: For C2.7-style expression-resume cleanup, a successful `holbuild(targets=["vyperTypeStmtSoundnessTheory"])` is not terminal proof evidence by itself. Follow it with a source/theory-index audit for `cheat`, `FAIL_TAC`, and suspended/unfinalized fragments, then compare any remaining obligations with structured PLAN coverage before closing the component.
works_when: Use when a build/audit component or broad cleanup leaf is active and prior dossier shows build-through cheats were possible.
evidence:
- episode:E0264
- tool_output:TO_type_system_rewrite-20260525T153549Z_m59961_t001

## L1844 scope='C2.7' tags=audit,cheat,call-target,source-classification
shape: C2.7 clean build plus two cheat lines near final call-target Resume blocks.
pattern: When C2.7 audit reports cheats at `vyperTypeStmtSoundnessScript.sml` lines ~16714 and ~16766, source inspection identifies them as `Expr_Call_ExtCall` and `Expr_Call_RawCallTarget`. These are covered by the active non-internal call-target expression branch leaf; proceed to prove those exact Resume blocks rather than replanning coverage.
works_when: Use after a clean `vyperTypeStmtSoundnessTheory` build still has exactly these two source-level cheats and C2.7 is active.
evidence:
- tool_output:TO_type_system_rewrite-20260525T153549Z_m59972_t001
- tool_output:TO_type_system_rewrite-20260525T153549Z_m59972_t002
- tool_output:TO_type_system_rewrite-20260525T153549Z_m59973_t003

## L1845 scope='C2.7' tags=ExtCall,RawCallTarget,template,boundary-helper,call-target
shape: Remaining C2.7 cheats are ExtCall/RawCallTarget Resume blocks after a clean focused build.
pattern: For the final C2.7 call-target cheats, use the neighboring expression Resume templates as the proof interface: unfold one `evaluate_def`, apply the eval_exprs IH, case-split the args result, derive target-specific runtime facts, then call a tail/boundary helper. Avoid deep `run_ext_call`/raw-call unfolding in the Resume consumer; if no boundary helper exists, add/escalate a small helper rather than proving internals inline.
works_when: Use when `vyperTypeStmtSoundnessTheory` builds but `vyperTypeStmtSoundnessScript.sml` still has cheats at `Expr_Call_ExtCall` and/or `Expr_Call_RawCallTarget`, and C2.7 is active.
evidence:
- tool_output:TO_type_system_rewrite-20260525T153549Z_m59993_t001
- tool_output:TO_type_system_rewrite-20260525T153549Z_m59993_t002
- tool_output:TO_type_system_rewrite-20260525T153549Z_m59993_t003

## L1847 scope='C2.7' tags=audit,grep,cheat,suspend,proof-integrity
shape: Broad grep for `cheat|FAIL_TAC|suspend` returns only early suspend skeleton lines while real cheats are later in the file.
pattern: For C2.7 final call-target audit, do not rely on a low-limit broad grep over `cheat|FAIL_TAC|suspend`: the suspend skeleton around lines 5557-5596 can consume the result budget before the actual ExtCall/RawCallTarget cheats. Use targeted reads/greps around `Expr_Call_ExtCall` and `Expr_Call_RawCallTarget`, or raise the grep limit and inspect the full output before closing.
works_when: Use when auditing `vyperTypeStmtSoundnessScript.sml` after a focused build succeeds but C2.7 may still have build-through cheats.
evidence:
- tool_output:TO_type_system_rewrite-20260525T153549Z_m60085_t002
- tool_output:TO_type_system_rewrite-20260525T153549Z_m60082_t002

## L1849 scope='C2.7' tags=ExtCall,boundary-helper,retired-reference,run_ext_call,proof-template
shape: ExtCall tail proof needs guidance beyond existing local account-preservation helpers.
pattern: Old retired `vyperTypeSoundnessHelpersScript.sml` contains a commented ExtCall chain proof skeleton and current `vyperEvalPreservesImmutablesDomScript.sml` contains live ExtCall pipeline factoring. Use these only as design references for a fresh local tail theorem in `vyperTypeStmtSoundnessScript.sml`: a current proof should compose local helpers such as `run_ext_call_accounts_well_typed` and should not depend on retired/commented theorems or copy old-stack assumptions wholesale.
works_when: C2.7 ExtCall cheat is active and the Resume proof has reached the post-`eval_exprs` success tail involving `run_ext_call`/`extract_call_result`.
evidence:
- tool_output:TO_type_system_rewrite-20260525T153549Z_m60265_t003
- tool_output:TO_type_system_rewrite-20260525T153549Z_m60265_t004
- tool_output:TO_type_system_rewrite-20260525T153549Z_m60264_t001

## L1851 scope='C2.7' tags=ExtCall,call-target,boundary-helper,handoff,run_ext_call,account-preservation
shape: C2.7 ExtCall Resume cheat remains after a clean focused build; helper block near lines 9417-9497 has account-preservation pieces.
pattern: For C2.7 ExtCall, first prove/use a consumer-facing tail boundary rather than unfolding external-call internals in the Resume. Existing local helpers cover the account-preservation pieces: `run_ext_call_accounts_well_typed`, `extract_call_result_accounts_well_typed`, and `guarded_make_ext_call_state_accounts_well_typed`. The Resume should unfold one evaluator step, consume eval_exprs IH, derive `exprs_runtime_typed`/ExtCall static facts, and call the tail theorem. If this boundary theorem expands into `run_ext_call`/rollback/ABI internals or creates a >4KB goal, checkpoint and ask for boundary redesign.
works_when: C2.7 active, source still has `Expr_Call_ExtCall` cheat, and the post-eval_exprs success branch reaches `run_ext_call`/`extract_call_result`.
evidence:
- tool_output:TO_type_system_rewrite-20260525T153549Z_m63394_t001
- tool_output:TO_type_system_rewrite-20260525T153549Z_m63394_t002
- tool_output:TO_type_system_rewrite-20260525T153549Z_m63394_t003
- episode:E1333

## L1852 scope='C2.7' tags=ExtCall,boundary-helper,pipeline,immutables-dom,proof-template
shape: ExtCall statement-soundness tail boundary needs pipeline shape without inlining external-call internals in the Resume.
pattern: A live proof reference for ExtCall pipeline factoring exists in `vyperEvalPreservesImmutablesDomScript.sml`: `extcall_inner_pipeline_imm_dom` and `extcall_pipeline_preserves_imm_dom` split the monadic ExtCall tail at get_self_code/build_calldata/run_ext_call and then delegate the post-run inner pipeline to a helper. For C2.7 ExtCall statement soundness, use this as the shape for a local consumer-facing tail theorem, combined with local account helpers (`run_ext_call_accounts_well_typed`, `extract_call_result_accounts_well_typed`, `guarded_make_ext_call_state_accounts_well_typed`), rather than unfolding `run_ext_call`/ABI/rollback directly in `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall]`.
works_when: Use when proving the `Expr_Call_ExtCall` Resume cheat and the post-`eval_exprs` success branch reaches `run_ext_call`/`extract_call_result`; if the helper proof itself becomes >4KB or unfolds rollback/ABI internals, checkpoint and request boundary redesign.
evidence:
- tool_output:TO_type_system_rewrite-20260525T153549Z_m63832_t001
- tool_output:TO_type_system_rewrite-20260525T153549Z_m63831_t002
- tool_output:TO_type_system_rewrite-20260525T153549Z_m63832_t004

## L1853 scope='C2.7' tags=ExtCall,static-typing,tail-boundary,argument-shape
shape: ExtCall tail theorem needs static argument/value extraction from `well_typed_expr_def`.
pattern: For `Call ty (ExtCall is_static (_,arg_types,ret_ty)) args drv`, `well_typed_expr_def` gives `ty = ret_ty`, `well_typed_exprs env args`, optional driver result type, and `MAP expr_type args = BaseT AddressT :: arg_types` for static calls or `BaseT AddressT :: BaseT (UintT 256) :: arg_types` for non-static calls. Use this to prove small runtime-destination facts (`dest_AddressV` for target, and `dest_NumV` for value when non-static) before calling the ExtCall tail boundary; do not derive these facts by unfolding the whole evaluator tail.
works_when: Use in C2.7 ExtCall Resume after eval_exprs IH yields `exprs_runtime_typed env args vs` and the static `well_typed_expr` clause has been stripped.
evidence:
- tool_output:TO_type_system_rewrite-20260525T153549Z_m64510_t003
- tool_output:TO_type_system_rewrite-20260525T153549Z_m64508_t001

## L1854 scope='C2.7' tags=ExtCall,ABI,dependency,tail-boundary,decode-return
shape: ExtCall tail theorem needs to type `lift_sum_runtime (evaluate_abi_decode_return tenv ret_type returnData)` result.
pattern: `vyperTypeStmtSoundnessScript.sml` does not currently list `vyperTypeABI` as an ancestor, but `vyperTypeABI` proves `evaluate_abi_decode_well_typed`. For C2.7 ExtCall, add/import the narrow ABI typing dependency as needed and prove a local `evaluate_abi_decode_return_well_typed` helper from `evaluate_abi_decode_return_def` before attacking the full tail theorem. This keeps ABI internals out of the Resume and tail proof.
works_when: Use in the ExtCall success branch after `run_ext_call` returns success and the evaluator either decodes return data or delegates to the driver expression; `evaluate_type tenv ret_type = SOME tv` follows from `well_formed_type env.type_defs ty` plus `ty = ret_ty`.
evidence:
- tool_output:TO_type_system_rewrite-20260525T153549Z_m64611_t003
- tool_output:TO_type_system_rewrite-20260525T153549Z_m64621_t001
- tool_output:TO_type_system_rewrite-20260525T153549Z_m64620_t001

## L1855 scope='C2.7' tags=ExtCall,args-runtime,dest_AddressV,dest_NumV,well_typed_expr_def
shape: After eval_exprs IH, ExtCall needs target/value extraction from `exprs_runtime_typed env args vs`.
pattern: Mirror the local `send_args_runtime_typed_dest`, `selfdestruct_args_runtime_typed_dest`, and `create_args_runtime_typed_dest` lemmas: use `exprs_runtime_typed_def` plus the ExtCall `MAP expr_type` shape from `well_typed_expr_def` to prove `dest_AddressV (HD vs) = SOME target_addr` and, for non-static calls, `dest_NumV (HD (TL vs)) = SOME amount`. This should be a small helper and should not unfold the ExtCall evaluator tail.
works_when: Use in `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall]` immediately after eval_exprs IH yields `exprs_runtime_typed env args vs` and the static/non-static argument-type equation has been stripped from `well_typed_expr_def`.
evidence:
- tool_output:TO_type_system_rewrite-20260525T153549Z_m64610_t001
- tool_output:TO_type_system_rewrite-20260525T153549Z_m64611_t002

## L1856 scope='C2.7' tags=ExtCall,args-runtime,LIST_REL,exprs_runtime_typed,dest_AddressV
shape: ExtCall args-runtime destructor helper fails after `rw[exprs_runtime_typed_def]` because list variable names disappear.
pattern: When proving ExtCall args destructors from `exprs_runtime_typed env args vs` plus `MAP expr_type args = BaseT AddressT :: ...`, do not destruct `vs` after a broad `rw[exprs_runtime_typed_def]` if the simplifier has already expanded and renamed the list. Either destruct `args`/`vs`/type lists before the broad rewrite, or use the live head facts produced by the rewrite: `evaluate_type ... (BaseT AddressT) = SOME tv` and `value_has_type tv y` close `∃target_addr. dest_AddressV y = SOME target_addr` by `evaluate_type_def`, `value_has_type_def`, and `dest_AddressV_def`.
works_when: Use for `extcall_static_args_runtime_typed_dest` and analogous non-static ExtCall destructor proofs where holbuild shows live head variables such as `y`, `tv`, `h` instead of the original `vs`.
evidence:
- tool_output:TO_type_system_rewrite-20260525T153549Z_m64678_t001
- episode:E1334

## L1861 scope='C2.7' tags=holbuild,tooling,strict-parse,blocked
shape: Pre-HOL holbuild option rejection: `holbuild: unknown build option: --strict-parse`
pattern: When holbuild rejects `--strict-parse`, no HOL theory has been parsed and no verified-prefix proof state exists. Treat it as an operational tooling blocker: do not edit proofs, do not ask the strategist for proof decomposition, and propose a tooling_bug blocked outcome unless tooling changed or the operator explicitly requests one retest.
works_when: Applies only to this exact pre-HOL option rejection, especially when PLAN remains active/beginable but holbuild produces no HOL goal state.
evidence:
- tool_output:TO_type_system_rewrite-20260528T153317Z_m68185_t001
- tool_output:TO_type_system_rewrite-20260528T153317Z_m68176_t001
- episode:E1337
