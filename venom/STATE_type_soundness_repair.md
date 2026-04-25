# STATE: Type Soundness Repair

## Overall Status: In-progress — Raise3 Resume block proof

## Build State
- vyperTypeSoundnessHelpersTheory: BUILDS (with 2 existing CHEATs)
- vyperTypeSoundnessTheory: FAILS at Raise3 Resume block

## Raise3 Root Cause Analysis (3 sessions, 6+ attempts)

### The Fundamental Problem
After `mp_tac >> rewrite_tac[ev_Raise3] >> simp_tac std_ss[bind_apply, BETA_THM]`,
the goal contains a nested case expression `(case eval_expr cx e st of ...) = (res, st') ⇒ conclusion`.
After `strip_tac`, this goes into assumptions as a single assumption containing the full
nested case expression. Subsequent `Cases_on \`eval_expr cx e st\`` creates branches,
but the assumption with the case expression can't be simplified by gvs because
the case expression is deeply nested — each step (get_Value, lift_option_type) has
its own INL/INR branches. The variable `st'` remains unresolved because the
simplifier can't push through all the nested case splits at once.

### Why Assert3 Works But Raise3 Doesn't
Assert3 uses `tp_bind_err_tac` (defined at line 978) which:
1. `strip_tac` — pushes the guard into assumptions
2. `POP_ASSUM STRIP_ASSUME_TAC` — splits conjunctions
3. `rpt BasicProvers.VAR_EQ_TAC` — resolves `st' = s3` etc.
4. State preservation lemmas + not_return + not_type_error_tac

**Raise3 can't use tp_bind_err_tac** because it's defined AFTER Raise3's Resume block (line 727).

### Three Approaches Tried
1. **strip_tac + Cases_on + gvs[bridge lemmas]** (original): After strip_tac, the case expression
   is in assumptions. Cases_on creates branches, but state variables (st') can't be
   resolved because gvs can't simplify all nested case levels at once. Fails with
   `state_well_typed st'` unsolved — st' never gets equated to a concrete state.

2. **strip_tac + Cases_on + specialized IH + bridge lemmas BEFORE gvs[toplevel_value_typed_def]**:
   Avoids expanding toplevel_value_typed_def (which creates conditional assumptions).
   Uses explicit `qspecl_then` to get toplevel_value_typed tv tyv, then bridge lemmas.
   Still fails because st' stays abstract — the case expression in assumptions constrains
   st' but gvs/Cases_on can't push the equalities through.

3. **No strip_tac, keep case expression in goal** (Assert3 pattern without tp_bind_err_tac):
   Keeps the nested case expression in the goal where Cases_on can operate.
   After `reverse (Cases_on q) >> simp_tac (srw_ss()) [] >- (INR handler)`,
   the `>-` FAILS because the INR handler (drule_all + strip_tac + CONJ_TAC) can't
   solve all conjuncts: the goal/subgoal shape after Cases_on + simp is different
   from what the simple handler expects. Error: "first subgoal not solved by second tactic".

### The Fix: Move tp_bind_err_tac BEFORE Raise3
The simplest fix: move the `tp_bind_err_tac` definition (and `not_return_tac`,
`not_type_error_tac`, `swt_resolve_state_tac` which it depends on) to BEFORE the
first Resume block that needs it. Then Raise3 can use the same pattern as Assert3.

**Alternative: Inline tp_bind_err_tac into Raise3.** This is more self-contained
but duplicates code. Given that 50+ blocks need the same pattern, moving the
definition is better.

### Raise3 Proof Structure (after fix)
```
rewrite_tac[ev_Raise3] >>
simp_tac std_ss [bind_apply, BETA_THM] >>
Cases_on `eval_expr cx e st` >>
reverse (Cases_on `q`) >> simp_tac (srw_ss()) [] >>
TRY (tp_bind_err_tac >> NO_TAC) >>
(* INL case: apply P7 IH, bridge lemmas, resolve step-by-step *)
first_x_assum drule_all >> strip_tac >>
first_x_assum (qspecl_then [`tv`] mp_tac) >> simp[] >> strip_tac >>
`expr_type e ≠ NoneT` by simp[] >>
imp_res_tac evaluate_type_not_NoneT_imp_not_NoneTV >>
imp_res_tac evaluate_type_BaseT_imp_not_ArrayTV >>
imp_res_tac toplevel_value_typed_not_ArrayRef >>
simp_tac (srw_ss()) [get_Value_def, return_def] >>
(* get_Value succeeds on Value v *)
imp_res_tac value_has_type_StringT_dest_StringV_NEQ_NONE >>
simp_tac (srw_ss()) [dest_StringV_def, lift_option_type_def, return_def] >>
(* raise *)
simp[raise_def, return_def] >>
swt_resolve_state_tac >>
rpt CONJ_TAC >> TRY not_return_tac >> TRY not_type_error_tac
```

## Existing CHEATs (must remove eventually)
1. `eval_expr_not_HashMapRef` Call case (helpers ~line 6823)
2. `functions_well_typed_body_full` (helpers ~line 620)

## What NOT to Try
- DON'T use `strip_tac` after bind_apply + BETA_THM without also using `tp_bind_err_tac`-style resolution afterwards — leaves `st'` abstract
- DON'T use `gvs[toplevel_value_typed_def]` to establish bridge lemma conditions — creates conditional assumptions imp_res_tac can't match
- DON'T use `gvs[ev_Raise3, bind_apply, AllCaseEqs(), get_Value_def, lift_option_type_def]` — 104s timeout
- DON'T use `Cases_on \`tv\`` for `∃v'. tv = Value v'` — 3 branches, gvs can't close impossible ones
- DON'T use `tp_stmt_no_return_tac` for Raise3 — leaves disconnected `e'` error variable
- DON'T skip `strip_tac` step without adjusting INR handler — subgoal shape changes, handler fails

## Key Lemmas (verified to exist in vyperTypeSoundnessHelpersTheory)
- `toplevel_value_typed_not_ArrayRef` — ∃v. tv = Value v (needs tyv ≠ NoneTV, ∀t b. tyv ≠ ArrayTV t b)
- `toplevel_value_typed_no_ArrayTV_get_Value` — get_Value succeeds + state unchanged
- `value_has_type_StringT_dest_StringV_NEQ_NONE` — dest_StringV ≠ NONE
- `get_Value_state` — state unchanged by get_Value
- `lift_option_type_state` — state unchanged by lift_option_type
- `evaluate_type_BaseT_imp_not_ArrayTV` — BaseT ⇒ not ArrayTV
- `evaluate_type_not_NoneT_imp_not_NoneTV` — not NoneT ⇒ not NoneTV

## Key Tactics (defined in vyperTypeSoundnessScript.sml)
- `tp_bind_err_tac` (line 978): strip + VAR_EQ + state lemmas + not_return + not_type_error
- `not_type_error_tac` (line 214): multi-strategy no-TypeError (ACCEPT, simp, IH, bridge lemmas)
- `not_return_tac` (line ~190): no-return disjunct
- `swt_resolve_state_tac` (line ~240): state preservation from IH

## Remaining Resume Blocks After Raise3
All 50+ blocks need no-TypeError proofs. Raise3 is the first failing block.

## Next Priority
1. **Move tactic definitions** (`tp_bind_err_tac`, `not_return_tac`, `not_type_error_tac`, `swt_resolve_state_tac`) BEFORE Raise3's Resume block in the file
2. Rewrite Raise3 to use the Assert3 pattern with `tp_bind_err_tac`
3. Rebuild — identify next failing block
4. Apply pattern to remaining blocks

## Provability Assessment
The theorem is TRUE. Raise3 must show: if you raise with a well-typed string expression,
the result is never a TypeError (it's always an AssertException). This is trivially true
since the evaluation chain (eval_expr → get_Value → dest_StringV → raise) never produces
TypeError when the expression is well-typed. The proof failure is purely tactical.
