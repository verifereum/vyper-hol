# STATE: Type Soundness Repair

## Overall Status: In-progress — Raise3 proof needs correct Resume block tactic

## Build State
- vyperTypeSoundnessHelpersTheory: BUILDS (with 2 existing CHEATs)
- vyperTypeSoundnessTheory: FAILS at Raise3 Resume block

## Current Proof File State
- `eval_stmt_Raise3_success` helper lemma added with CHEAT (line ~726-736)
- Raise3 Resume block (line ~738-750) has broken tactic (`qpat_x_assum` fails)
- Need to: (1) fix helper lemma proof, (2) fix Resume block tactic

## Raise3 Failure Diagnosis (8+ attempts this session)

### WHY Raise3 IS TRUE (mathematical reasoning)
`eval_stmt cx (Raise (RaiseReason e)) st` does:
1. `eval_expr cx e st` → `(INL tv, s1)` (by IH: state/typing preserved)
2. `get_Value tv s1` → `(INL v, s1)` (state unchanged; well-typed tv is `Value v` not HashMapRef/ArrayRef)
3. `lift_option_type (dest_StringV v) "not StringV" s1` → `(INL s, s1)` (state unchanged; StringT value means dest_StringV ≠ NONE)
4. `raise (AssertException s) s1` → `(INR (AssertException s), s1)` (state unchanged; NOT TypeError)
So: `st' = s1`, `res = INR (AssertException s)`, no TypeError, no ReturnException.

### FAILED APPROACH 1: gvs[ev_Raise3, bind_apply, AllCaseEqs()] + rpt pop_assum
- 104s timeout — AllCaseEqs creates 8+ case branches, endless simplification

### FAILED APPROACH 2: tp_stmt_no_return_tac ev_Raise3 wts_Raise3 []
- Leaves `∀s. e' ≠ Error (TypeError s)` unsolved — fresh error variable e' disconnected from typing assumptions

### FAILED APPROACH 3: Step-by-step Cases_on with simp_tac std_ss [Once bind_apply]
- `qpat_x_assum` fails after first `mp_tac` + strip_tac — assumption consumed/transformed

### FAILED APPROACH 4: simp[bind_def] + Cases_on eval_expr + Cases_on r
- FIRST_ASSUM error — after expansion, no matching assumption for drule

### FAILED APPROACH 5: Helper lemma eval_stmt_Raise3_success in helpers file
- 170s rebuild each iteration; lemma proof itself fails (metis can't close; simp explosion)

### FAILED APPROACH 6: Helper lemma in main file with cheat + simplified Resume block
- Cheat lemma works but Resume block tactic still wrong (qpat_x_assum fails)

## THE CORRECT APPROACH (not yet implemented)
Two sub-problems must be solved independently:

### Step A: Prove `eval_stmt_Raise3_success` (helper lemma)
Move to helpers file (after existing CHEATs). Use this proof strategy:
```
rpt gen_tac >> strip_tac >>
qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
simp[cj 8 evaluate_def, bind_apply, AllCaseEqs(), raise_def, return_def] >>
strip_tac >>
gvs[get_Value_def, lift_option_type_def, dest_StringV_def] >>
rpt (pop_assum mp_tac >> simp[] >> strip_tac) >>
imp_res_tac toplevel_value_typed_not_ArrayRef >>
gvs[] >>
imp_res_tac value_has_type_StringT_dest_StringV_NEQ_NONE >>
gvs[] >>
metis_tac[]
```
Key: DON'T include get_Value_def/lift_option_type_def in the initial simp — let AllCaseEqs create the branches, then use rpt pop_assum to simplify each. Add state preservation lemmas (get_Value_state, lift_option_type_state) in the final gvs.

### Step B: Fix Raise3 Resume block to use helper lemma
```sml
Resume eval_preserves_swt[Raise3]:
  rpt gen_tac >> strip_tac >>
  gvs[wts_Raise3] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[ev_Raise3, bind_apply, AllCaseEqs(), raise_def, return_def] >>
  strip_tac >>
  rpt (pop_assum mp_tac >> simp[] >> strip_tac) >>
  gvs[toplevel_value_typed_def, evaluate_type_not_NoneT_imp_not_NoneTV,
      evaluate_type_BaseT_imp_not_ArrayTV, get_Value_def,
      lift_option_type_def, dest_StringV_def,
      value_has_type_StringT_dest_StringV_NEQ_NONE,
      get_Value_state, lift_option_type_state] >>
  rpt CONJ_TAC >> TRY not_return_tac >> TRY not_type_error_tac
QED
```
Key insight: The `simp[ev_Raise3, bind_apply, AllCaseEqs()]` doesn't time out IF we don't also expand get_Value_def/lift_option_type_def in the same simp call. The `rpt (pop_assum mp_tac >> simp[] >> strip_tac)` then iteratively simplifies each branch.

## Build Time Critical Issue
- Adding lemmas to END of vyperTypeSoundnessHelpersScript.sml forces 170s full rebuild
- Solution: Put helper lemma in the MAIN proof file (vyperTypeSoundnessScript.sml), before the Resume block. Only 20s rebuild.

## Existing CHEATs (must remove eventually)
1. `eval_expr_not_HashMapRef` Call case (helpers ~line 6823)
2. `functions_well_typed_body_full` (helpers ~line 620)

## Key Lemmas (verified to exist)
- `toplevel_value_typed_not_ArrayRef` — gives `∃v. tv = Value v`
- `toplevel_value_typed_no_ArrayTV_get_Value` — get_Value can't INR on well-typed
- `value_has_type_StringT_dest_StringV_NEQ_NONE` — dest_StringV ≠ NONE
- `get_Value_state` — state unchanged: `st' = st`
- `lift_option_type_state` — state unchanged: `st' = st`
- `evaluate_type_BaseT_imp_not_ArrayTV` — BaseT ⇒ not ArrayTV
- `evaluate_type_not_NoneT_imp_not_NoneTV` — not NoneT ⇒ not NoneTV

## What NOT to Try
- DON'T include get_Value_def or lift_option_type_def in initial simp[bind_apply, AllCaseEqs()] — causes explosion
- DON'T use gvs[AllCaseEqs(), get_Value_def, lift_option_type_def] inside bind chains — state variable explosion
- DON'T use `simp_tac std_ss [bind_def]` + `Cases_on q` — creates assumption matching failures
- DON'T put helper lemma at END of helpers file — 170s rebuild penalty; put in main file instead
- DON'T use `imp_res_tac toplevel_value_typed_no_ArrayTV_get_Value` when only INL assumption exists — adds conditional fact

## Oracle Feedback
- Used plan_oracle once this session for Raise3
- Claude Opus plan: suggested using exact Raise1/Raise2 pattern (gvs + rpt pop_assum) — FAILED because Raise3's bind chain is deeper and creates more complex goals after expansion
- Gemini plan: suggested step-by-step Cases_on after bind_apply — FAILED due to qpat_x_assum failures after assumption consumption
- Both models underestimated the state variable explosion problem with AllCaseEqs + deep bind chains
- Key insight from practice: separating the initial simp (bind_apply + AllCaseEqs + raise + return) from the definition expansions (get_Value_def, lift_option_type_def, dest_StringV_def) and doing them in separate gvs/rpt-pop_assum phases is the approach most likely to work

## Remaining Resume Blocks After Raise3
All 50+ blocks need no-TypeError proofs. Raise3 is the first failing block. Once Raise3 pattern is established, it applies to all bind-chain blocks.

## Next Priority
1. Fix eval_stmt_Raise3_success proof (in main file, not helpers)
2. Fix Raise3 Resume block using helper
3. Rebuild — identify next failing block
4. Apply pattern to remaining blocks
