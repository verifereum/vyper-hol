# STATE: Type Soundness Repair

## Overall Status: eval_expr_not_HashMapRef — subgoal count mismatch blocks build

## Build State
- vyperTypeSoundnessHelpersTheory: FAILS — `eval_expr_not_HashMapRef` proof structure wrong (subgoal count mismatch in `>|`)
- vyperTypeSoundnessTheory: FAILS (depends on helpers)
- Two cheats in helpers file: line 614 (functions_well_typed_body_full, pre-existing) + 4 cheats in Resume blocks

## Key Progress This Session

### PROVED helpers (all in vyperTypeSoundnessHelpersScript.sml):
- `extcall_none_not_HashMapRef` (Triviality, line ~6698): drv=NONE ExtCall never returns HashMapRef
- `extcall_some_not_HashMapRef` (Triviality, line ~6717): drv=SOME ExtCall not HashMapRef given drv IH
- `subscript_not_HashMapRef` (Triviality, line ~6672): Subscript not HashMapRef given base IH
- These replace the old `extcall_not_HashMapRef` Triviality

### Resume blocks already proved (no cheats):
P0_Name, P0_BareGlobalName, P0_FlagMember, P0_Literal, P0_StructLit,
P0_Attribute, P0_Builtin, P0_Pop, P0_TypeBuiltin (9 of 13)

### Resume blocks with cheats (4):
P0_TopLevelName, P0_IfExp, P0_Subscript, P0_Call

## BLOCKING ISSUE: `>|` subgoal count mismatch

The `gen_tac >> Induct_on `e` >> rpt conj_tac >| [...]` fails with "lists of different length". 

**Root cause:** Don't know exact number of subgoals after `Induct_on `e` >> rpt conj_tac`. The expr_induction principle has `∀P0 P1 P2 P3 P4 P5`. After instantiation, `rpt conj_tac` splits the antecedent conjunction. But the number of conjunctions depends on how the induction principle decomposes, which differs from my assumed 25.

**FIX NEEDED:** Next session must determine the EXACT subgoal count. Options:
1. Use HOL4 interactively: set a dummy goal and apply `gen_tac >> Induct_on `e` >> rpt conj_tac` then count subgoals
2. Use `>-` chaining instead of `>|` (avoids needing exact count)
3. Use the approach from `eval_expr_toplevel_wf` which works with `ho_match_mp_tac evaluate_ind` — count its `>|` entries (34 trivial + 20 expr + 2 trivial = 56)
4. Count conjunctions in `expr_induction` antecedent programmatically

## Proof Plans for Remaining Cheats

### P0_TopLevelName:
```
rpt strip_tac >>
qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
simp[Once evaluate_def, bind_def, return_def, lift_option_type_def,
     lift_option_def, lift_sum_def, UNCURRY, PULL_EXISTS, AllCaseEqs()] >>
rpt strip_tac >> Cases_on `tv` >> gvs[is_HashMapRef_def] >-
(PairCases_on `p` >> gvs[] >>
 imp_res_tac lookup_global_HashMapRef >>
 gvs[well_typed_expr_def] >>
 drule_all env_consistent_toplevel_hashmap >> gvs[])
```

### P0_IfExp:
```
rpt strip_tac >>
qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
simp[Once evaluate_def, hmr_blast_defs, is_HashMapRef_def] >>
rpt strip_tac >> gvs[well_typed_expr_def] >-
(first_x_assum irule >> simp[]) >>
first_x_assum irule >> simp[]
```

### P0_Subscript:
```
rpt strip_tac >> irule subscript_not_HashMapRef >> HINT_EXISTS_TAC >> simp[]
```

### P0_Call (ExtCall case):
```
rpt strip_tac >> Cases_on `c` >> gvs[] >| [
  imp_res_tac intcall_returns_Value >> gvs[is_HashMapRef_def],  (* IntCall *)
  Cases_on `o'` >> gvs[] >-  (* ExtCall *)
    (imp_res_tac extcall_none_not_HashMapRef >> simp[]) >>
    (irule extcall_some_not_HashMapRef >> simp[] >>
     rpt strip_tac >> first_x_assum irule >> simp[] >>
     irule env_consistent_scopes_immutables >> HINT_EXISTS_TAC >> simp[] >>
     conj_tac >- metis_tac[update_accounts_scopes] >>
     metis_tac[update_transient_scopes]),
  imp_res_tac call_simple_returns_Value >> gvs[is_HashMapRef_def],  (* Send *)
  imp_res_tac rawcalltarget_returns_Value >> gvs[is_HashMapRef_def],
  imp_res_tac rawlog_returns_Value >> gvs[is_HashMapRef_def],
  (* RawRevert: monad expand *)
  (qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
   simp_tac (srw_ss()) [Once evaluate_def, hmr_blast_defs, is_HashMapRef_def, AllCaseEqs()] >>
   rpt strip_tac >> gvs[]),
  imp_res_tac selfdestruct_returns_Value >> gvs[is_HashMapRef_def],
  imp_res_tac createtarget_returns_Value >> gvs[is_HashMapRef_def]
]
```

## Other Cheat
- Line 614: `functions_well_typed_body_full` — pre-existing, not priority

## Key Helpers (all PROVED)
- subscript_not_HashMapRef, extcall_none_not_HashMapRef, extcall_some_not_HashMapRef
- All _returns_Value lemmas (14, [local] Theorems in same file)
- env_consistent_toplevel_hashmap, env_consistent_scopes_immutables
- lookup_global_HashMapRef, well_typed_opt_SOME
- update_accounts_scopes, update_transient_scopes (from vyperScopePreservationTheory)
- evaluate_subscript_success_not_HashMapRef
- hmr_blast_defs, hmr_case_defs, ev_expr_cjs (val bindings)

## What NOT To Try
- DON'T use `ho_match_mp_tac evaluate_ind` — guarded ExtCall IH intractable
- DON'T use `simp[evaluate_def]` without `Once` — HANGS
- DON'T use `Induct_on 'e'` with single quotes — HOL4 needs backtick `e`
- DON'T guess `>|` list length — must determine exact count first
- DON'T use `>|` with wrong length — causes "lists of different length" error
- DON'T need to re-create extcall/subscript helpers — already proved in file

## PROVABILITY
Theorem IS TRUE. HashMapRef only from TopLevelName (lookup_global for hashmaps). All other constructors return Value or propagate IH. ExtCall: env_consistent preserved (scopes/immutables only), drv IH applies directly.

## Proof Integrity Notes
- extcall_none_not_HashMapRef and extcall_some_not_HashMapRef replace the old extcall_not_HashMapRef
- The old extcall_not_HashMapRef, eval_expr_not_HashMapRef_ind, all old Resume blocks have been DELETED from the file
- The Induct_on approach avoids the guarded IH matching problem entirely
