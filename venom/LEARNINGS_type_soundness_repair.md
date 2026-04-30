# LEARNINGS: Type Soundness Repair

## IH Application: The Critical Pattern (Sessions 9-13, 18)

### BROKEN: `qspecl_then` with backtick terms
Backtick terms get FIXED types at SML definition time. Type mismatches → SPECL HOL_ERR
→ FIRST_ASSAM error. ROOT CAUSE of 57 block failures in sessions 9-11.

### WORKING: `qpat_x_assum + drule_all`
```sml
qpat_x_assum `∀env st res st'. well_typed_expr _ _ ∧ _ ⇒ _` drule_all >> strip_tac
```
Auto-matches ALL antecedents, no explicit term construction needed.

### CRITICAL: `first_x_assum drule_all` consumes WRONG IH (Session 18)
When multiple ∀-IHs exist, `first_x_assum` picks the NEWEST. In Append block line 1176,
it consumed the guarded P7 IH (containing `eval_base_target`) instead of P5 IH,
leaving no `eval_base_target` ∀-assumption for later steps. This was misdiagnosed
as a `qspecl_then` failure for 3 sessions.

**Fix: Use `qpat_x_assum` with a pattern that ONLY matches the target IH.**
For P5: `∀env st res st'. (∃ty. well_typed_target _ _ ty) ∧ _ ⇒ _`
For guarded P7: use `first_x_assum (fn th => if is_forall (concl th) andalso can (find_term ...) (concl th) then ...)`

### AVOID: `first_assum ACCEPT_TAC` for guard discharge (Session 16)
Definition changes altered assumption ordering. Use `qpat_x_assum` with specific pattern.

### AVOID: `qpat_x_assum` with primed variables (Session 18)
`` `!s'' loc' sbs' t'. eval_base_target _ _ _ = _ ==> _` ``
produces `Q_TAC0` parsing error. Use `first_x_assum (fn th => ...)` with `same_const` test instead.

### CANNOT use `same_const` inside `fn th => ...` in proof quotations (Session 18)
`` same_const u ``eval_base_target`` `` inside a `fn th => if ...`
continuation in a proof sequence may not resolve correctly — `FIRST_ASSAM` error.
The constant reference works in top-level SML but may fail inside proof context.
**Alternative:** Use a let-bound predicate function defined OUTSIDE the proof.

## SUBGOAL ORDERING (Sessions 14-15)

### After `Cases_on 'q'`, INL is FIRST, INR is SECOND
```sml
Cases_on `q` >> simp_tac (srw_ss()) [] >>
TRY (strip_tac >> ... >> NO_TAC) >>
(* Now only the INL case remains *)
```

## VARIABLE NAMING AFTER SIMPLIFICATION (Session 16)

### gvs[] changes variable structure
After gvs, variable naming differs from old expectations.
NEVER assume variable names — check with `hol_state_at`.

### `Cases_on v` where `v : value` → TIMEOUT
Use boundary lemmas (`switch_BoolV_cases`, `toplevel_value_typed_BoolT_inv`) instead.

## ABSTRACTION: Use boundary lemmas, not definition unfolding

### switch_BoolV: use `switch_BoolV_cases`, not `switch_BoolV_def`
Also available: `switch_BoolV_preserves`, `switch_BoolV_error`

## SML SYNTAX PITFALLS (Session 15)
- `&&` = simpset conjunction, NOT boolean. Use `andalso`.
- `PRED_ASSUM` takes `term -> bool`, not `thm -> bool`.

## hol_check_proof vs holmake (Session 15)
`hol_check_proof` does NOT verify Resume blocks. Only `holmake` does.

## KEY INSIGHT: simp_tac can SOLVE entire blocks (Session 13)
After augmented simpset (exception_distinct, error_distinct at line 26),
try `rewrite_tac[ev_X] >> simp_tac (srw_ss()) [bind_apply, BETA_THM] >> gvs[]`
BEFORE adding manual IH application.

## Guarded IH discharge (14+ blocks)
OLD (fragile): `qpat_x_assum ... (qspecl_then [...] mp_tac) >> impl_tac >- ACCEPT_TAC`
NEW (robust): Define `apply_guarded_ih` tactic that uses `first_x_assum (fn th => ...)`
with a let-bound predicate.

## INR error propagation pattern (30+ instances)
```sml
strip_tac >>
qpat_x_assum `∀env st res st'. well_typed_expr _ _ ∧ _ ⇒ _` drule_all >>
strip_tac >> no_return_from_eval >> gvs[]
```

## Constructor distinctness (no-TypeError/no-return conjuncts)
`augment_srw_ss[rewrites [exception_distinct, error_distinct]]` at line 26.

## State lemmas for pure operations (10+ uses)
materialise_state, get_Value_state, lift_option_type_state, etc.
All: `st' = st`. Use: `imp_res_tac X_state >> gvs[]`

## materialise TypeError chain (7 lemmas in helpers)
materialise TypeError → is_HashMapRef → tyv = NoneTV → NoneT → well_typed excludes NoneT

## IH function-specific patterns for qpat_x_assum
- P7 (eval_expr): `∀env st res st'. well_typed_expr _ _ ∧ _ ⇒ _`
- P0 (eval_stmt): `∀env ret_ty st res st'. well_typed_stmt _ _ _ ∧ _ ⇒ _`
- P1 (eval_stmts): `∀env ret_ty st res st'. well_typed_stmts _ _ _ ∧ _ ⇒ _`
- P2 (eval_iterator): `∀env typ st res st'. well_typed_iterator _ _ _ ∧ _ ⇒ _`
- P3 (eval_target): `∀env st res st'. ∃ty. well_typed_atarget _ _ ty ∧ _ ⇒ _`
- P5 (eval_base_target): `∀env st res st'. ∃ty. well_typed_base_target _ _ ty ∧ _ ⇒ _`
- P5 (alt for target): `∀env st res st'. (∃ty. well_typed_target _ _ ty) ∧ _ ⇒ _`
- P8 (eval_exprs): `∀env st res st'. well_typed_exprs _ _ ∧ _ ⇒ _`
- P6 (eval_for): 7 ∀-vars → needs separate pattern

## evaluate_builtin_well_typed (FULLY PROVED, in vyperBuiltinTyping)
Takes `accounts_well_typed acc` precondition. Covers ALL builtin cases.

## Key boundary lemmas (defined in main file, lines 217-233)
- evaluate_type_BaseT_inv, toplevel_value_typed_for_BaseT
- toplevel_value_typed_BoolT_inv, value_has_type_BoolT_inv
