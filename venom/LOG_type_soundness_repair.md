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

L002: [tp_bind_err_tac fix] 3 attempts all fail — drule_all, drule_all+conj, drule all hang on rich IH contexts
  - Root cause: first_x_assum + drule/drule_all iterates ALL 10+ IH assumptions
  - Each IH has 7+ antecedents → combinatorial explosion
  - imp_res_tac before gvs[] adds clutter making it worse
  - Next: try asm_simp_tac (srw_ss()) or per-block explicit qpat_x_assum IH selection
  - Build times out at 1800s, 26+ blocks prove (simple ones), 29 blocks hang

L002: [tp_bind_err_tac] FAILED[need_helper]: 3 approaches all hang on rich IH contexts
  - drule_all: combinatorial explosion (7 antecedents × 10+ IHs)
  - drule_all+conj_cleanup: same explosion, ordering irrelevant  
  - drule_only: first_x_assum picks wrong IH, partial match expensive
  - Root cause: first_x_assum + drule/drule_all on rich assumption contexts
  - Next: try gvs[] directly (srw_ss auto-instantiates IHs), or tp_pure_err_tac
L003: [KEY][existing tactics] Discovered tp_pure_err_tac (line 334) and discharge_ih_tac
  (line 380) already in file but UNUSED. tp_pure_err_tac is designed exactly for
  pure error propagation (INR cases). discharge_ih_tac does targeted MATCH_MP
  IH application. Either could fix tp_bind_err_tac without new code.

## Session 4: drule_at (Pos last) fix

L060: [KEY][tp_bind_err_tac] `drule_at (Pos last)` confirmed fast: build goes from 1800s timeout to 155s
  - Verified `drule_at : match_position -> thm_tactic` exists in HOL4's Tactic.sig
  - `Pos last` matches LAST antecedent (unique eval equality) vs FIRST (generic well_typed_X)
  - dxrule_at also removes the matched assumption (useful for clean context)
L061: [tp_bind_err_tac] FAILED[wrong_decomposition]: direct drule→drule_at(Pos last) substitution breaks Assert3 (line 1147). Because tp_bind_err_tac conflates INR error and INL success, changing which IH matches succeed in INR case pollutes context for subsequent INL proof steps.
L062: [KEY][tp_bind_err_tac] ROOT CAUSE: tp_bind_err_tac is wrong decomposition. Must split into:
  - `close_inr_err_tac`: strip + VAR_EQ + dxrule_at(Pos last) + rpt strip_tac + ACCEPT_TAC + gvs[] — closes INR branches completely
  - `tp_inl_tac`: drule_at(Pos last) + state lemmas + IH retry — for INL continuation
L063: [Assert3]** Was never actually proved. Listed as proved in -j8 build but fails in -j1. Other "proved" blocks may have same issue.
L064: [not_type_error_tac] Contains `first_x_assum drule_all` (lines 254, 262) that could also hang, but these run in post-IH contexts where fewer IHs remain. Kept as-is for now.

L004: [close_inr_err_tac] Defined close_inr_err_tac + close_pure_inr_err_tac, replaced 23 call sites → BUILD FAILS at Raise3 line 870: close_inr_err_tac leaves 5 residual subgoals. Two issues: (1) IH variable capture after dxrule_at, (2) missing no-return resolution. Fix: add gvs[] for variable elimination + not_return_tac for no-return.
