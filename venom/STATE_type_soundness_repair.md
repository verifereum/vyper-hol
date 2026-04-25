# STATE: Type Soundness Repair

## Overall Status: In-progress — ReturnSome FIXED, Raise2 next blocker

## Build State
- vyperTypeSoundnessHelpersTheory: BUILDS OK (pre-existing cheat on `eval_expr_not_HashMapRef` Call case)
- vyperTypeSoundnessTheory: FAILS at Raise2 (second failing Resume block after ReturnSome was fixed)

## KEY BREAKTHROUGH this session

**Root cause found and fixed**: `not_type_error_tac` Strategy 3 had TWO bugs:
1. **Missing VAR_EQ substitution**: After `spose_not_then strip_assume_tac` introduces `e' = Error(TypeError s')`, this equality was NOT substituted into the `materialise cx tv s'' = (INR e', s')` assumption. So `materialise_type_error_imp_NoneTV` couldn't match. Fixed by adding `rpt BasicProvers.VAR_EQ_TAC` after `spose_not_then`.
2. **Missing guard**: Strategy 3 (spose_not_then) applied to ALL goals, not just those with materialise equations. This irrevocably changed goals where simpler strategies (ACCEPT from IH) would work. Fixed by guarding with `qhdtm_assum `materialise` (fn _ => ...)`.

**Verified proof chain** (tested interactively in HOL):
```
spose_not_then strip_assume_tac  →  e' = Error(TypeError s), goal F
rpt BasicProvers.VAR_EQ_TAC      →  materialise cx tv s'' = (INR (Error(TypeError s)), s')
imp_res_tac materialise_type_error_imp_NoneTV  →  tyv = NoneTV
gvs[]                            →  evaluate_type ... = SOME NoneTV, toplevel_value_typed tv NoneTV
imp_res_tac evaluate_type_NoneTV_imp_NoneT  →  expr_type e = NoneT
gvs[]                            →  well_typed_expr + expr_type e = NoneT + eval_expr cx e st = (INL tv, s'')
imp_res_tac well_typed_expr_NoneT_eval_not_HashMapRef  →  ~is_HashMapRef tv
imp_res_tac materialise_not_HashMapRef_no_type_error  →  contradiction → DONE
```

## ReturnSome: FIXED ✓
Strategy 3 now works for the materialise case subgoal. ReturnSome block passes.

## Raise2: Current Blocker
After `gvs[ev_Raise2, raise_def]`, goal is:
```
(∀s. e' ≠ Error (TypeError s)) ∧
∀v ret_tv. e' = ReturnException v ∧ ... ⇒ value_has_type ret_tv v
```
**Diagnosis**: `not_type_error_tac` with `TRY` can solve the TypeError conjunct but leaves the return-typing conjunct. Need `not_return_tac` too, or split with CONJ_TAC before applying.

**Fix**: Change Raise2 block to:
```sml
Resume eval_preserves_swt[Raise2]:
  gvs[ev_Raise2, raise_def] >> TRY not_type_error_tac >> TRY not_return_tac
QED
```
Or more robustly, split first:
```sml
  gvs[ev_Raise2, raise_def] >> conj_tac >- not_type_error_tac >> not_return_tac
```

## Current not_type_error_tac Structure (working)
1. `ACCEPT_TAC` — IH-derived ∀s. e'≠Error(TypeError s) already in assumptions
2. `drule_all >> strip_tac >> gvs[]` — IH discharge
3. `qhdtm_assum 'materialise' (fn _ => spose_not_then ... VAR_EQ_TAC ... contradiction chain)` — only fires when materialise in assumptions
4. `gvs[toplevel_value_typed_def, ...]` then retry ACCEPT/drule
5. `imp_res_tac materialise_Value_no_type_error / materialise_not_HashMapRef_no_type_error` etc.
6. Bridge lemmas for dest_StringV/BytesV/NumV/AddressV etc.
7. Final `gvs[raise_def, return_def, ...]` catch-all

## Pattern: Remaining ~50 Resume blocks
Most blocks follow one of these patterns:
- **Simple constructor distinctness**: `gvs[...]` suffices (augment_srw_ss handles)
- **IH propagation**: ∀s. e'≠Error(TypeError s) already from IH → ACCEPT_TAC
- **materialise case**: Strategy 3 chain (now working)
- **Sub-evaluation bind**: need both `not_return_tac` and `not_type_error_tac`
- **Value typing remaining**: some blocks have extra conjuncts beyond no-TypeError

## Key Pre-existing Cheats
- `eval_expr_not_HashMapRef` Call case: CHEAT (line 6822 of helpers)
- `functions_well_typed_body_full`: CHEAT (line ~620 of helpers)

## What NOT to Try
- DON'T use `>-` inside Resume blocks (type error with gentactic)
- DON'T expand `evaluate_def` without `Once` — HANGS
- DON'T apply `spose_not_then` without a guard checking materialise is in assumptions
- DON'T forget `rpt BasicProvers.VAR_EQ_TAC` after spose_not_then
- DON'T use `qhdtm_x_assum` for guard (it consumes the assumption)

## Oracle Feedback
- Previous oracle suggested IH discharge + constructor distinctness — partially correct
- augment_srw_ss handles constructor distinctness, ACCEPT_TAC handles IH
- The critical fix (VAR_EQ substitution after spose_not_then) was discovered by
  interactive debugging, not oracle suggestion
