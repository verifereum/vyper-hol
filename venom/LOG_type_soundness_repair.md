# LOG: Type Soundness Repair

L001: [Assert3] imp_res_tac toplevel_value_typed_for_BaseT in `by` block → FAILED (silent match failure: assumptions have `expr_type e` not `BaseT bt`)
L002: [Assert3] gvs[] before `by` block → TIMEOUT (Assert3 context with guarded IH too rich for gvs)
L003: [Assert3] fs[] to cross-rewrite → doesn't substitute `expr_type e` in `evaluate_type` assumption
L004: [Assert3] ML trick: nested qpat_x_assum → TIMEOUT (nested ML quotations break)
L005: [Assert3] metis_tac[toplevel_value_typed_for_BaseT] → TIMEOUT (too many assumptions)
L006: [Assert3] irule toplevel_value_typed_for_BaseT_expr_type >> simp[] → FAILED (simp can't discharge antecedent subgoals in `by` block)
L007: [Assert3] RULE_ASSUM_TAC(ONCE_REWRITE_RULE[th]) → WORKS for rewriting, but `by` block still fails at line 1117
L008: [helpers] toplevel_value_typed_for_BaseT_expr_type → COMPILED (3-antecedent variant matching IH output shape)
L009: [Assert3] KEY INSIGHT: `by` block is wrong decomposition. Need to inline derivation after RULE_ASSUM_TAC.
L010: [Assert3] RULE_ASSUM_TAC(ONCE_REWRITE_RULE[th]) → WORKS for rewriting `expr_type e → BaseT BoolT` in all assumptions
L011: [Assert3] `by` block still fails at line 1117 after RULE_ASSUM_TAC → NEED: inline derivation without `by`
L012: [KEY] After IH application, `evaluate_type (get_tenv cx) (expr_type e) = SOME tyv` + `expr_type e = BaseT bt` are SEPARATE assumptions. Must use RULE_ASSUM_TAC to merge them before `imp_res_tac` can match.
L013: [KEY] `by` blocks are fragile in rich proof contexts — imp_res_tac silently fails inside them with no diagnostic. Prefer inline derivation.
L014: [helpers] `toplevel_value_typed_for_BaseT_expr_type` COMPILED: matches exact IH shape with `expr_type e` in separate assumption
L015: [Assert3] gvs[] causes TIMEOUT when guarded IH for e' is in context — use RULE_ASSUM_TAC instead
L016: [Assert3] ALL Category A blocks will need same RULE_ASSUM_TAC pattern for `expr_type e` substitution
L017: [KEY] gvs[]/fs[] do NOT substitute function application equalities into other assumptions. Only variable equalities. `expr_type e = BaseT BoolT` is NOT substituted. Must use RULE_ASSUM_TAC.
L018: [KEY] toplevel_value_typed_BoolT_inv is the BEST boundary lemma for BoolT cases: gives direct `?b. tv = Value (BoolV b)` witness after evaluate_type_BaseT_inv
L019: [Assert3] irule toplevel_value_typed_for_BaseT_expr_type inside `by` block → FAILED: creates `∃bt e tenv tyv. ...` subgoals that ACCEPT_TAC can't discharge
L020: [Assert3] qexistsl_tac inside `by` block → FAILED: `by` subproof context prevents proper witness provision
L021: [Assert3] Correct approach confirmed via interactive testing: RULE_ASSUM_TAC → evaluate_type_BaseT_inv → toplevel_value_typed_BoolT_inv → Cases_on b (NO by blocks)
L022: [Assert3] e' branch BUG: `first_x_assum (qspec_then \`x\` strip_assume_tac)` picks wrong assumption for IH specialization. Needs `drule_all` on pattern-matched IH instead.
L023: [Assert3] e' branch BUG: toplevel_value_typed_BoolT_inv is WRONG for StringT. Must use general path (evaluate_type_not_NoneT_imp_not_NoneTV + evaluate_type_BaseT_imp_not_ArrayTV + Cases_on)
L003: [Assert3] Fixed guarded IH for e' branch using IfExp_True pattern (Q.SPECL + impl_tac + disch_then drule_all). Replaced 3 failed approaches (qspec_then, drule, drule+disch_then). Also fixed AnnAssign INR/INL case split: `>> TRY (.. >> NO_TAC)` → `>-`. AnnAssign not yet build-verified.
L003: [Assert3] PROVED: Fixed guarded IH for e' branch using IfExp_True pattern (Q.SPECL + impl_tac + disch_then drule_all). Also fixed StringT classification (was using BoolT_inv incorrectly).
L004: [AnnAssign] IN PROGRESS: Fixed INR/INL case split from `>> TRY (.. >> NO_TAC)` to `>-`. Needs build verification.
L005: [KEY] Guarded IH discharge pattern: Q.SPECL + impl_tac + disch_then drule_all. NOT drule or qspec_then.
L006: [KEY] `>> TRY (.. >> NO_TAC)` after case splits silently fails — use `>-` instead.
L007: [AnnAssign] 5+ FAILED attempts to fix INR branch handling
  - Attempt 1: `>- (tp_bind_err_tac)` → THEN1 failure (tp_bind_err_tac can't solve guarded IH)
  - Attempt 2: `>- (imp_res_tac materialise_state >> gvs[return_def] >> rpt CONJ_TAC >> ... >> not_type_error_tac)` → FIRST_ASSUM failure in not_type_error_tac (no typing assumptions in context)
  - Attempt 3: Derive toplevel_value_typed before materialise split via `qpat_x_assum ∀tv. INL _ = INL tv ==> _ (mp_tac o SIMP_RULE...) >> disch_then drule` → DISCH_THEN failure
  - Attempt 4: `simp[bind_def, AllCaseEqs(), raise_def]` style → drule_all fails (no matching IH pattern)
  - RESOLUTION: Suspended AnnAssign. Need to derive typing BEFORE case splits.
L008: [KEY] For materialise INR branches: must derive `toplevel_value_typed x tyv` BEFORE `Cases_on materialise`, otherwise `not_type_error_tac` has no information to exclude TypeError.
L009: [Append] FAILED at build: `FIRST_ASSUM` error in INR branch. Same root cause as AnnAssign.
  - The `>> TRY (tp_bind_err_tac >> NO_TAC)` pattern after eval_base_target case split silently fails
  - The `TRY (imp_res_tac materialise_state >> ... >> imp_res_tac materialise_error >> gvs[] >> NO_TAC)` for materialise INR doesn't prove no-TypeError
L010: [Oracle] 3-model consultation: all agree on (1) fix INR pattern, (2) prove Category A first, (3) prove cheat lemmas in order. Key Gemini insight: error propagation is simpler (no values to typecheck); derive no-TypeError from IH. Key GPT-5.5 insight: factor materialise-no-TypeError into reusable helper.

## Session N: Assessment only — no proofs completed

- holmake passed for helpers, failed for main theory (Append block FIRST_ASSUM error)
- Root cause: TRY (tp_bind_err_tac >> NO_TAC) pattern — same as documented in previous sessions
- Navigated proof state: INR branch of eval_base_target in Append needs explicit `>-` handling
- Fix is mechanical: replace TRY with `>- (drule_all IH >> strip_tac >> gvs[])`
- No edits made this session due to timing

L008: [Append] FAILED[wrong_decomposition]: TRY (tp_bind_err_tac >> NO_TAC) silently fails on INR branch from eval_base_target. FIRST_ASSUM error in subsequent tactics. Fix: replace all 3 TRY blocks with explicit `>-` INR handling using drule_all of sub-evaluation IH.
L009: [KEY][Append] tp_bind_err_tac is fundamentally broken for INR branches — it tries too many strategies and when none match, TRY in caller makes failure invisible. Replace with explicit `>-` pattern.
L010: [KEY] Build order matters — 29 subgoals remain, build stops at FIRST failing Resume block. Fix Append first, then iterate.
L054: [Append] TRY (tp_bind_err_tac >> NO_TAC) → FAILED: tp_bind_err_tac doesn't close INR subgoals with new 4-conjunct IH
L055: [Append] Replace with >- (INR handler) → FAILED: type error (gentactic vs tactic) then "first subgoal not solved"
L056: [Append] >- (cheat)  → FAILED: same "first subgoal not solved" — wrong subgoal targeted or precedence issue
L057: [KEY][Append] Interactive HOL session confirmed: after reverse(Cases_on res_bt)>>simp_tac, 2 subgoals exist (INR first, INL second). tp_bind_err_tac's drule_all >> strip_tac works but gvs[] doesn't close all new conjuncts
L058: [KEY] Fix should be in tp_bind_err_tac itself (add CONJ_TAC + not_return_tac + not_type_error_tac after drule_all+strip_tac+gvs[]), not per-block. This would fix all 21+ TRY instances at once.
