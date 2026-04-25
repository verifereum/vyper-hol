# STATE: Type Soundness Repair

## Overall Status: In-progress — Raise3 proof needs correct step-by-step case splitting with state preservation

## Build State
- vyperTypeSoundnessHelpersTheory: BUILDS (with 2 existing CHEATs)
- vyperTypeSoundnessTheory: FAILS at Raise3 block

## Current Proof Decomposition (Raise3)
Raise3 = `eval_stmt cx (Raise (RaiseReason e)) st` which does:
```
do tv <- eval_expr cx e;
   v <- get_Value tv;
   s <- lift_option_type (dest_StringV v) "not StringV";
   raise (AssertException s)
od
```
Three bind steps, each pure (state unchanged).

## Raise3 Failure Diagnosis (5+ attempts this session)

### Attempt 1: Manual expansion following ReturnSome pattern
- `simp[bind_def, AllCaseEqs(), ...] >> strip_tac` then `drule_all` IH
- Result: `state_well_typed s'⁴'` unsolved — `AllCaseEqs()` creates fresh state vars not equated
- Diagnosis: `AllCaseEqs()` on `get_Value_def`/`lift_option_type_def` introduces disconnected state variables

### Attempt 2: `imp_res_tac` bridge lemmas before expansion
- Apply IH, then `imp_res_tac toplevel_value_typed_no_ArrayTV_get_Value`, then `drule get_Value_state`
- Result: `drule get_Value_state` fails — bridge lemma added CONDITIONALLY (antecedents undischarged)
- Diagnosis: `imp_res_tac` on `toplevel_value_typed_no_ArrayTV_get_Value` can't match against INL assumption; adds conditional fact with undischarged antecedents `tyv ≠ NoneTV` and `∀t b. tyv ≠ ArrayTV t b`

### Attempt 3: `gvs` with all defs + `rpt (pop_assum mp_tac >> simp[] >> strip_tac)` (Raise1/Raise2 style)
- Result: 104s timeout / goal explosion — deeper bind chain (3 binds vs 1 for Raise1/Raise2) creates massive disjunction
- Diagnosis: `gvs[AllCaseEqs(), get_Value_def, lift_option_type_def]` creates exponential case explosion

### Attempt 4: Step-by-step `Cases_on` without `AllCaseEqs()`
- `Cases_on eval_expr`, `Cases_on get_Value`, `Cases_on dest_StringV` etc.
- Result: `>-` failures — subgoals not fully solved by supplied tactics
- Diagnosis: Wrong subgoal ordering; `>-` demands full solution; need `>-` only when sure of solution

## THE CORRECT APPROACH (not yet implemented)
Step through the bind chain one `Cases_on` at a time:
1. `rewrite_tac[ev_Raise3]` then `simp_tac std_ss [bind_apply, BETA_THM]`
2. `Cases_on 'eval_expr cx e st'` → INR case: simple propagate; INL case: continue
3. Apply IH on INL case, derive `toplevel_value_typed tv tyv`, `tyv ≠ NoneTV`, `∀t b. tyv ≠ ArrayTV t b`
4. `Cases_on 'get_Value tv s1'` → INR case: use bridge lemma directly (`irule` or `metis_tac`) ; INL case: `drule get_Value_state >> strip_tac`
5. `Cases_on 'dest_StringV v'` → NONE: use `value_has_type_StringT_dest_StringV_NEQ_NONE` ; SOME: `drule lift_option_type_state >> strip_tac`
6. Resolve final state with equalities derived from steps 4-5

KEY: Do NOT use `AllCaseEqs()` or `gvs[get_Value_def]` — these cause state variable explosion. Use explicit `Cases_on` and `get_Value_state`/`lift_option_type_state` to derive state equalities.

## Key Lemmas (verified to exist)
- `toplevel_value_typed_no_ArrayTV_get_Value` — proved in helpers
- `value_has_type_StringT_dest_StringV_NEQ_NONE` — proved in helpers
- `get_Value_state` — proved in vyperStatePreservationScript.sml
- `lift_option_type_state` — proved in vyperStatePreservationScript.sml
- `evaluate_type_BaseT_imp_not_ArrayTV` — proved in helpers
- `evaluate_type_not_NoneT_imp_not_NoneTV` — proved in helpers

## Existing CHEATs (must remove eventually)
1. `eval_expr_not_HashMapRef` Call case (helpers ~line 6823)
2. `functions_well_typed_body_full` (helpers ~line 620)

## Remaining Resume Blocks After Raise3
All 50+ blocks need no-TypeError proofs. Raise3 is the first failing block. The pattern learned here (step-by-step Cases_on + state lemmas) applies to all bind-chain blocks.

## What NOT to Try
- DON'T use `AllCaseEqs()` with `get_Value_def`/`lift_option_type_def` — causes state variable explosion
- DON'T use `gvs[get_Value_def]` inside bind chains — same explosion
- DON'T use `tp_stmt_no_return_tac` for bind-chain cases — it does AllCaseEqs before IH
- DON'T use `imp_res_tac` on `toplevel_value_typed_no_ArrayTV_get_Value` when only INL assumption exists — adds conditional fact
- DON'T use `simp[Once run_block_def]` — HANGS
- DON'T use `fs[evaluate_type_NoneTV_imp_NoneT]` — use `imp_res_tac` instead

## Oracle Feedback
Not used this session — all attempts were direct proof work based on STATE from previous session.

## Next Priority
1. Fix Raise3 using step-by-step Cases_on approach (see THE CORRECT APPROACH above)
2. Rebuild after Raise3 fixed — identify next failing block
3. Apply pattern to remaining blocks
4. Eventually: remove existing CHEATs
