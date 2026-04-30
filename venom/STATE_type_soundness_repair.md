# STATE: Type Soundness Repair

## STRATEGIC PLAN (Session 13)

### PRIORITY 1: Fix IH application infrastructure (HIGH RISK)

**Root cause confirmed:** `apply_eval_ih` uses `qpat_x_assum + qspecl_then` with backtick terms.
The backtick terms get FIXED types at SML definition time. When applied in different proof
contexts, SPECL raises HOL_ERR on type mismatch. `FIRST` doesn't handle these exceptions
from sub-tactics, so all alternatives fail → FIRST_ASSUM error.

**Working pattern (verified in ReturnSome, line 752):**
```sml
qpat_x_assum `!env st res st'. well_typed_expr _ _ /\ _ ==> _`
  drule_all >> strip_tac
```
This works because `drule_all` automatically matches ALL IH antecedents against
assumptions, specializing `res` and `st'` correctly without explicit terms.

**Fix plan:**
1. Replace `apply_eval_ih` with `drule_all`-based version
2. Test on Raise3 first (simplest failing block)
3. If `drule_all` is too slow, fall back to `drule` (matches only first antecedent)

**New `apply_eval_ih`:**
```sml
fun apply_eval_ih res_term st_term =
  FIRST [
    qpat_x_assum `∀env st res st'. well_typed_expr _ _ ∧ _ ⇒ _` drule_all,
    qpat_x_assum `∀env ret_ty st res st'. well_typed_stmt _ _ _ ∧ _ ⇒ _` drule_all,
    qpat_x_assum `∀env ret_ty st res st'. well_typed_stmts _ _ _ ∧ _ ⇒ _` drule_all,
    qpat_x_assum `∀env typ st res st'. well_typed_iterator _ _ _ ∧ _ ⇒ _` drule_all,
    qpat_x_assum `∀env st res st'. ∃ty. well_typed_atarget _ _ ty ∧ _ ⇒ _` drule_all,
    qpat_x_assum `∀env st res st'. EVERY _ _ ∧ _ ⇒ _` drule_all,
    qpat_x_assum `∀env st res st'. ∃ty. well_typed_base_target _ _ ty ∧ _ ⇒ _` drule_all,
    qpat_x_assum `∀env st res st'. well_typed_exprs _ _ ∧ _ ⇒ _` drule_all
  ] >> strip_tac
```

NOTE: `res_term` and `st_term` are kept for API compat but IGNORED. `drule_all`
handles specialization automatically.

### PRIORITY 2: Fix `close_inr_err_tac` and `tp_bind_err_tac`

Both call `apply_eval_ih` with explicit result/state terms. After the `drule_all` fix,
these arguments are ignored. The tactics should still work since `drule_all` handles
specialization.

### PRIORITY 3: Fix guarded IH blocks (MEDIUM RISK)

Blocks like Append, Assign, AugAssign use:
```sml
qpat_x_assum `!s'' tv t. eval_expr cx e s'' = (INL tv, t) ==> _`
  (fn ih => mp_tac (ih |> Q.SPECL [`st`, `Value (BoolV F)`, `r`]))
```
This also uses explicit terms. Replace with:
```sml
qpat_x_assum `!s'' tv t. eval_expr cx e s'' = (INL tv, t) ==> _`
  (fn ih => mp_tac ih >> impl_tac >- first_assum ACCEPT_TAC) >> strip_tac
```
Or use `discharge_ih_tac` (already defined, lines 380-405).

### PRIORITY 4: Fix remaining ~55 blocks

After infrastructure fixes, rebuild and fix any remaining failures one by one.

### PRIORITY 5: Prove 6 cheats in helpers file

## BLOCK STATUS (Session 12)

### WORKING (25 blocks):
Pass, Continue, Break, ReturnNone, ReturnSome, Raise1, Raise2, Assert1, Assert2,
Log, Expr, stmts_nil, stmts_cons, BaseTarget, TupleTarget,
targets_nil, targets_cons, NameTarget, BareGlobalNameTarget,
TopLevelNameTarget, AttributeTarget, for_nil, Name, Literal, exprs_nil

### FAILING (55+ blocks — all due to `apply_eval_ih` SPECL bug):
Raise3: FIRST_ASSUM error (confirmed: SPECL type mismatch in apply_eval_ih)
Assert3: `Cases_on b` fails after wrong IH application; also `by` tactic fails
Append: `Cases_on x` fails — "No var with name x" after wrong IH drule_all
All others: Untested individually but same root cause (IH application)

## KEY INSIGHT: `qpat_x_assum + drule_all` IS the fix

ReturnSome (line 752) proves this pattern works:
```
qpat_x_assum `!env st res st'. well_typed_expr _ _ /\ _ ==> _` drule_all >> strip_tac
```
- `drule_all` automatically matches `eval_expr cx e st = (res,st')` against assumptions
- This correctly specializes `res` and `st'` to the values in the current proof context
- No explicit term construction needed → no type mismatch possible
- This is the ONLY working IH application pattern in the entire file

## WHAT NOT TO TRY
- `qspecl_then` with backtick terms — TYPE ERRORS at SML definition time
- `first_x_assum drule_all` — picks wrong IH when multiple ∀-assumptions exist
- `first_x_assum + SPECL` — same type error issue, plus FIRST_ASSUM when all fail
- Python scripts that cheat outer blocks containing nested suspends — DESTROYS inner labels
- `simp[evaluate_def]` without `Once` — HANGS
- `metis_tac` with many assumptions — TIMES OUT
- `>-` / `>|` in Resume blocks — produces gentactic, not tactic
- `first_x_assum drule_all` in rich IH contexts — HANGS or picks wrong IH

## IH PATTERNS (for drule_all matching)
- P7 (eval_expr): `∀env st res st'. well_typed_expr _ _ ∧ _ ⇒ _`
- P0 (eval_stmt): `∀env ret_ty st res st'. well_typed_stmt _ _ _ ∧ _ ⇒ _`
- P1 (eval_stmts): `∀env ret_ty st res st'. well_typed_stmts _ _ _ ∧ _ ⇒ _`
- P2 (eval_iterator): `∀env typ st res st'. well_typed_iterator _ _ _ ∧ _ ⇒ _`
- P3 (eval_target): `∀env st res st'. ∃ty. well_typed_atarget _ _ ty ∧ _ ⇒ _`
- P4 (eval_targets): `∀env st res st'. EVERY _ _ ∧ _ ⇒ _`
- P5 (eval_base_target): `∀env st res st'. ∃ty. well_typed_base_target _ _ ty ∧ _ ⇒ _`
- P8 (eval_exprs): `∀env st res st'. well_typed_exprs _ _ ∧ _ ⇒ _`
- P6 (eval_for): `∀env typ ret_ty st res st'. ... ∧ eval_for _ _ _ _ _ st = (res,st') ⇒ _`

NOTE: P6 (eval_for) has 7 ∀-variables, not 4 or 5. It needs a separate pattern.

## CHEATS (6 in helpers file)
| Theorem | What |
|---------|------|
| env_consistent_pop_scope | Pop scope preserves env_consistent |
| env_consistent_preserves_tv | Eval preserves tv+env_consistent |
| bind_arguments_env_consistent | Call arg binding preserves env |
| set_immutable_well_typed | set_immutable preserves typing |
| assign_target_well_typed | Assignment replace preserves typing |
| eval_expr_not_HashMapRef | Well-typed eval not HashMapRef |

## KEY FILES
- Main theorem: semantics/prop/vyperTypeSoundnessScript.sml (~4053 LOC)
- Helpers: semantics/prop/vyperTypeSoundnessHelpersScript.sml (~7307 LOC, 6 cheats)
- Workdir: semantics/prop/
