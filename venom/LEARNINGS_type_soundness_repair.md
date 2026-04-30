# LEARNINGS: Type Soundness Repair

## CRITICAL: eval_expr INR error propagation for P0 goals (Sessions 37-38)

When a P0 (stmt) goal has an eval_expr INR branch, the IH gives state/env/accounts/
no-TypeError, but NOT no-ReturnException at type `unit + exception`. You MUST also
use `imp_res_tac eval_expr_not_return` to close the return-typing conjunct.

### Working pattern (from AugAssign lines 1337-1343):
```sml
TRY (strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
     first_x_assum drule_all >> strip_tac >>
     rpt CONJ_TAC >> TRY (first_assum ACCEPT_TAC) >>
     rpt strip_tac >> gvs[] >>
     imp_res_tac eval_expr_not_return >>
     first_x_assum (qspec_then `v` mp_tac) >>
     simp_tac (srw_ss()) [] >> NO_TAC)
```

### Why close_inr_err_tac fails for P0 goals:
close_inr_err_tac handles state/env/accounts/no-TypeError but NOT the P0-specific
return-typing conjunct `∀v ret_tv. res = INR (ReturnException v) ∧ ... ⇒ ...`.
This needs eval_expr_not_return to show the antecedent is impossible.

## CRITICAL: Applying guarded IH — BEFORE vs AFTER case split (Sessions 37-39)

When the P7 IH (for eval_expr) is guarded by an eval_target/eval_base_target
condition, it appears as:
```
eval_target cx g s'' = (INL gv, t) ⇒ ∀env st res st'. well_typed_expr ... ⇒ ...
```

**AugAssign approach (WORKS):** Apply guarded IH AFTER eval_expr case split,
inside the INL branch only (lines 1349-1354). INR TRY block uses
`first_x_assum drule_all` which finds another IH successfully.

**Assign_tgt approach (BROKEN in session 39):** Applying guarded IH BEFORE
case split makes `qpat_x_assum` remove the guarded form, leaving only the
unguarded form. But `qpat_x_assum` with `_` wildcards on the unguarded IH
pattern fails with Q_TAC0. Use `suspend` for both branches + explicit
specialization in each Resume block instead.

**Safe pattern for guarded IH specialization:**
```sml
qpat_x_assum `!s'' gv t. eval_target _ _ s'' = (INL gv,t) ==> _`
  (qspecl_then [`st`, `x`, `st_tgt`] mp_tac) >>
(impl_tac >- first_assum ACCEPT_TAC) >> strip_tac
```
The guard pattern `!s'' gv t. eval_target _ _ s'' = _ ==> _` works with `_`.
The unguarded IH pattern `!env st res st'. well_typed_expr _ _ /\ _ ==> _`
does NOT work with `_` — use `first_x_assum drule_all` or PRED_ASSUM instead.

## CRITICAL: close_inr_err_tac_for Fix (Session 34)

### `simp_tac (srw_ss()) []` CANNOT prove ∀-goals from ∀-assumptions
After applying an IH via `drule_all`, the conclusion `∀s. P s` exists as both
goal and assumption. But `simp_tac` can't match them because HOL4's bound
variables have different internal names (alpha-equivalence issue in simpset).

### FIX: strip_tac first, then ACCEPT_TAC, then pop_assum for contradictions
```sml
rpt (CONJ_TAC >> first_assum ACCEPT_TAC) >>
rpt strip_tac >>
TRY (first_x_assum ACCEPT_TAC) >>
rpt (pop_assum mp_tac >> simp[])
```

## CRITICAL: gvs Leaves Assumptions as Implication Antecedents (Session 36)

After `gvs[return_def]`, equalities can remain chained as `A ⇒ B ⇒ C ⇒ goal`.
FIX: `rpt strip_tac >> gvs[return_def]` (strip first, then gvs)

## Monadic Bind Chain Pattern (4 instances: Assign, AugAssign, Append, AnnAssign)

### Structure
All assignment-like statements follow the same monadic chain:
1. Evaluate target/location (eval_target or eval_base_target)
2. Evaluate expression (eval_expr)
3. Materialise or get_Value the result
4. assign_target
5. return ()

### INR branches: ALWAYS use AugAssign pattern (with eval_expr_not_return)
```sml
strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
qpat_x_assum `!env st res st'. well_typed_expr _ _ /\ _ ==> _`
  drule_all >> strip_tac >>
rpt CONJ_TAC >> TRY (first_assum ACCEPT_TAC) >>
rpt strip_tac >> gvs[] >>
imp_res_tac eval_expr_not_return >>
first_x_assum (qspec_then `v` mp_tac) >>
simp_tac (srw_ss()) []
```

### assign_target sub-proof: suspend _atwt
```sml
Cases_on `assign_target cx x (Replace v) r` >>
`state_well_typed r' /\ env_consistent env cx r'` by suspend "X_atwt" >>
reverse (Cases_on `q`) >> simp_tac (srw_ss()) [return_def] >>
... imp_res_tac (cj 1 assign_target_no_return) ...
```

## SML Type Inference for Tactics (Session 32)
Always add `: tactic` annotations to tactic definitions. `>>` is overloaded → SML infers gentactic instead of tactic.

## `>-` (THEN1) does NOT work inside Resume blocks (Session 39)
`>-` inside a Resume block body causes SML type inference to pick `gentactic`
instead of `tactic` — even with parenthesized subgoals. Error message:
"Can't unify ('a, 'b) gentactic * tactic to goal -> goal list * (thm list -> thm)".
FIX: Use `TRY + NO_TAC` pattern (like AugAssign) or `suspend` both branches.

## `>-` (THEN1) with `suspend` does NOT work (Session 38)
`suspend` doesn't solve subgoals inline - it creates Resume blocks.
Use `>- tac` only with tactics that solve the subgoal. For suspend, use
`>> suspend "name"` which applies to ALL remaining subgoals (since suspend
solves the current one and creates a named Resume block for it).

## Key Boundary Lemmas

### In vyperTypeSoundnessHelpersScript.sml:
- assign_target_well_typed: assign_target preserves state_well_typed + env_consistent
- assign_target_no_return: assign_target never returns ReturnException
- materialise_no_type_error, materialise_well_typed_no_type_error
- toplevel_value_typed_materialise: connects toplevel_value_typed → value_has_type after materialise
- evaluate_type_NoneTV_imp_NoneT, well_typed_expr_TopLevelName_NotNoneT
- well_typed_expr_NoneT_eval_not_HashMapRef

### In main file:
- evaluate_type_BaseT_inv, toplevel_value_typed_for_BaseT
- toplevel_value_typed_BoolT_inv, value_has_type_BoolT_inv

### In vyperBuiltinTyping:
- evaluate_builtin_well_typed: all builtin operations preserve typing

## State Preservation Lemmas (10+ uses)
All pure ops: `st' = st`. Use: `imp_res_tac X_state >> gvs[]`
- materialise_state, get_Value_state, lift_option_type_state
- lift_option_state, lift_sum_state, check_state
- type_check_state, switch_BoolV_state

## AVOID (confirmed failures)
- close_inr_err_tac for P0 goals with return-typing conjuncts
- `>-` (THEN1) inside Resume blocks — gentactic type inference error
- `>-` with `suspend` (suspend doesn't solve inline)
- `qpat_x_assum` with `_` wildcards in complex universal+implication patterns — Q_TAC0
  (works for simple guard patterns like `!s'' gv t. eval_target _ _ s'' = _ ==> _`)
  (fails for unguarded IH like `!env st res st'. well_typed_expr _ _ /\ _ ==> _`)
- qpat_x_assum with dot-notation — PARSE ERROR
- simp_tac (srw_ss()) [] for ∀-goals from ∀-assumptions — alpha-eq issue
- gvs[] on complex nested case expressions → TIMEOUT
- metis_tac[] on goals requiring ∀-instantiation → timeout
- irule on ¬ assumptions → spurious ∃ witness subgoals
- Unicode in quotations — Q_TAC0
- holmake with timeout < 600s
- Writing 5+ tactic lines without verifying with hol_state_at
- Guessing variable names after Cases_on — always inspect first
- Applying guarded IH before case split, then TRY for INR case
  (TRY fails → corrupts subgoal order → `>-` gets wrong subgoal)
- Manual INR error chains (drule_all + strip_tac + CONJ_TAC...) — USE AugAssign pattern
