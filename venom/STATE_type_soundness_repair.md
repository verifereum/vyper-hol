# STATE: Type Soundness Repair

## Overall Status: In-progress — Raise3 Resume block proof

## Build State
- vyperTypeSoundnessHelpersTheory: BUILDS (with 2 existing CHEATs)
- vyperTypeSoundnessTheory: FAILS at Raise3 Resume block

## Raise3 Current State
The step-by-step approach (modeled on Assert3) is the right decomposition but needs fixing.

### The Goal Shape After Initial Steps
After `rewrite_tac[ev_Raise3] >> simp_tac std_ss [bind_apply, BETA_THM] >> strip_tac`,
the antecedent contains the FULL nested case expression for the evaluation chain:
```
case eval_expr cx e st of
  (INL tv, s1) => case get_Value tv s1 of
    (INL v, s2) => case lift_option_type (dest_StringV v) ... s2 of
      (INL s, s3) => raise (AssertException s) s3
    | (INR e, s3) => (INR e, s3)
  | (INR e, s2) => (INR e, s2)
| (INR e, s1) => (INR e, s1)
```

### Step-by-Step Approach (Assert3 pattern)
1. `Cases_on \`eval_expr cx e st\`` → INR branch (dispatch with IH), INL branch (continue)
2. Apply IH for eval_expr → get `toplevel_value_typed tv tyv`, state preservation, no-TypeError
3. Show `tv = Value v'` using bridge lemmas
4. Rewrite `get_Value (Value v')` → `return v'` (no INR branch possible)
5. Show `dest_StringV v'` succeeds using `value_has_type_StringT_dest_StringV_NEQ_NONE`
6. Rewrite `lift_option_type (SOME s)` → `return s` (no INR branch possible)
7. Rewrite `raise (AssertException s)` → final conjuncts

### Current Failure: Step 3 — `tv = Value v'` not established
After `gvs[toplevel_value_typed_def, evaluate_type_not_NoneT_imp_not_NoneTV, evaluate_type_BaseT_imp_not_ArrayTV]`,
the assumptions become conditional (not simplified), e.g.:
`(∀t b. tyv ≠ ArrayTV t b) ⇒ tyv ≠ NoneTV ⇒ ∃v. tv = Value v`
But `imp_res_tac toplevel_value_typed_not_ArrayRef` can't match because the conditions
aren't established as simple assumptions — they're buried in implications.

### Fix: Apply bridge lemmas BEFORE gvs expansion
Instead of expanding `toplevel_value_typed_def` which creates conditional assumptions,
apply `toplevel_value_typed_not_ArrayRef` directly (it already has the conditions built in).
Then we get `∃v. tv = Value v` as a direct result.

**Correct step ordering for the INL tv branch:**
```
first_x_assum drule_all >> strip_tac >>
(* DON'T gvs[toplevel_value_typed_def] here *)
(* Instead apply the bridge lemma directly *)
imp_res_tac toplevel_value_typed_not_ArrayRef >>  (* gives ∃v. tv = Value v *)
gvs[get_Value_def] >>  (* now get_Value (Value v') = return v' *)
```

But `toplevel_value_typed_not_ArrayRef` requires `tyv ≠ NoneTV` and `∀t b. tyv ≠ ArrayTV t b`.
These come from: `evaluate_type_not_NoneT_imp_not_NoneT` (needs `expr_type e ≠ NoneT`,
which follows from `expr_type e = BaseT (StringT n)`) and `evaluate_type_BaseT_imp_not_ArrayTV`
(needs `evaluate_type (get_tenv cx) (BaseT (StringT n)) = SOME tyv`).

The key is to establish these facts IN ASSUMPTIONS before calling `imp_res_tac`:
```
(* Establish tyv ≠ NoneTV and ∀t b. tyv ≠ ArrayTV t b from IH result *)
`expr_type e ≠ NoneT` by simp[] >>
imp_res_tac evaluate_type_not_NoneT_imp_not_NoneTV >>
imp_res_tac evaluate_type_BaseT_imp_not_ArrayTV >>
(* Now conditions are in assumptions, bridge lemma fires *)
imp_res_tac toplevel_value_typed_not_ArrayRef >>
gvs[get_Value_def] >>
```

### Alternative: Use `toplevel_value_typed_no_ArrayTV_get_Value` directly
This lemma says: if `toplevel_value_typed tv tyv ∧ tyv ≠ NoneTV ∧ (∀t b. tyv ≠ ArrayTV t b)`
then `get_Value tv st = (INL v, st)` for some v AND `state unchanged`. This combines
steps 3+4 into one.

## Existing CHEATs (must remove eventually)
1. `eval_expr_not_HashMapRef` Call case (helpers ~line 6823)
2. `functions_well_typed_body_full` (helpers ~line 620)

## What NOT to Try
- DON'T use `tp_stmt_no_return_tac` for Raise3 — leaves disconnected `e'` error variable
- DON'T expand `toplevel_value_typed_def` in assumptions with `gvs` — creates messy conditional assumptions that bridge lemmas can't match
- DON'T use `gvs[ev_Raise3, bind_apply, AllCaseEqs(), get_Value_def, lift_option_type_def]` — causes 104s timeout from state variable explosion
- DON'T use `Cases_on \`tv\`` to prove `∃v'. tv = Value v'` — creates 3 branches including impossible ones that gvs can't close
- DON'T use `qpat_x_assum` deeply after `mp_tac`/`strip_tac` — assumptions get consumed/renamed
- DON'T use `tp_bind_err_tac` in Raise3 (defined AFTER Raise3 in the file)

## Key Lemmas (verified to exist)
- `toplevel_value_typed_not_ArrayRef` — gives `∃v. tv = Value v` (needs tyv ≠ NoneTV, tyv ≠ ArrayTV)
- `toplevel_value_typed_no_ArrayTV_get_Value` — get_Value always succeeds, returns INL + state unchanged
- `value_has_type_StringT_dest_StringV_NEQ_NONE` — dest_StringV ≠ NONE
- `get_Value_state` — state unchanged by get_Value
- `lift_option_type_state` — state unchanged by lift_option_type
- `evaluate_type_BaseT_imp_not_ArrayTV` — BaseT ⇒ not ArrayTV
- `evaluate_type_not_NoneT_imp_not_NoneTV` — not NoneT ⇒ not NoneTV

## Remaining Resume Blocks After Raise3
All 50+ blocks need no-TypeError proofs. Raise3 is the first failing block.

## Next Priority
1. Fix Raise3: apply bridge lemmas before gvs expansion (see fix above)
2. Rebuild — identify next failing block
3. Apply pattern to remaining blocks
