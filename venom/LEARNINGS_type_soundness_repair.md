# LEARNINGS: Type Soundness Repair

## CRITICAL: Never use `>-` for complex inline subproofs (Session 69)

`>-` requires COMPLETE solution. Any leftover subgoal is fatal. For anything
beyond `simp[]`/`gvs[]`, USE SUSPEND/RESUME.

## CRITICAL: `>>` after Cases_on applies to ALL subgoals (Sessions 69, 72, 73)

After case split, using `>> tac` applies to ALL subgoals. MUST use `>-` per branch.
EXCEPTION: `TRY close_inr_err_tac >>` after `reverse (Cases_on 'q')` is VALID.

## CRITICAL: Guarded IH blocks (If, IfExp, For) — don't use close_inr_err_tac

Only If, IfExp, For blocks have guarded IHs from eval_expr→push_scope composition.
In these blocks, `close_inr_err_tac` can't find the right IH because guarded P1 IHs
match the PRED_ASSUM predicate but `drule_all` fails on them. Handle INR case
explicitly with `>-` and targeted `qpat_x_assum`.
DO NOT modify close_inr_err_tac to handle guarded IHs — 5 approaches all failed.
See L028-L031 in LOG for detailed failure analysis.

## CRITICAL: qpat_x_assum REMOVES assumption before continuation (Session 84)

`qpat_x_assum pat tac` finds match, REMOVES it, then applies tac.
If tac fails, the assumption is GONE. This makes `FIRST [qpat_x_assum p1 drule_all,
qpat_x_assum p2 drule_all, ...]` UNSAFE — failure of first drule_all consumes the
first IH, then second qpat_x_assum matches next IH, cascade until all consumed.
FIX: Use `qpat_assum` (keeps assumption) in FIRST chains, or use explicit patterns
with `>-` to avoid ambiguity entirely.

## CRITICAL: `>> gvs[AllCaseEqs()] >-` type error (Session 75)

After `gvs[AllCaseEqs()]`, parenthesize: `Cases_on 'q' >- (..tacs..) >> suspend "INR"`

## CRITICAL: Guarded IH instantiation required before not_type_error_tac (Session 75)

eval_expr IH is guarded: `∀tv. INL x = INL tv ⇒ ...toplevel_value_typed tv tyv`.
MUST instantiate first. BUT after `gvs[AllCaseEqs()]`, the guarded IH may already
be resolved — check what assumptions exist before calling qpat_x_assum.

## CRITICAL: gvs changes goal shapes (Sessions 82, 84)

`gvs[AllCaseEqs()]` resolves guarded IHs (instantiating ∀tv variables).
`gvs[pair_case_thm, return_def]` auto-discharges conjuncts matching assumptions.
Both break positional ACCEPT_TAC patterns. Always check what gvs produced.

## CRITICAL: `first_assum ACCEPT_TAC` fails when conclusion structure changes

New conclusion has 6 conjuncts (swt, ec, awt, no-TE, no-ret, ret-typing).
After gvs auto-discharges some, remaining order differs from old expectations.
FIX: use explicit tactics instead of positional ACCEPT_TAC.

## CRITICAL: Fix shared tactics BEFORE individual blocks (Session 80)

`close_inr_err_tac` and `tp_bind_err_tac` used by MANY blocks. Fix ONCE → many blocks work.
BUT: close_inr_err_tac can only be fixed for unguarded-IH contexts. Guarded-IH
blocks need explicit handling, not shared tactic modification.

## CRITICAL: close_inr_err_tac needs VAR_EQ_TAC after no_return_from_eval (Session 82)

After `drule_all >> strip_tac >> no_return_from_eval`, add `rpt BasicProvers.VAR_EQ_TAC`
so variable names (like `st'` vs `r`) are equated, enabling ACCEPT_TAC on remaining conjuncts.

## CRITICAL: `qpat_assum` (without `_x_`) throws Q_TAC0/FIRST_ASSUM errors (Session 78)

8 instances in the file. `qpat_x_assum` does NOT produce this error.
Convert to `qpat_x_assum` one by one, but be CAREFUL: some code uses the
matched assumption to create a NEW assumption (e.g., Assign block wraps with
Q.EXISTS) — those MUST stay as `qpat_assum` to keep the original.

## CRITICAL: scope_bracket_preserves now includes accounts_well_typed (Session 84)

Extended to add `accounts_well_typed st_body.accounts` as hypothesis and
`accounts_well_typed (...).accounts` as conclusion. Consumers need to supply
the hypothesis (from P1 IH conclusion). If_True/If_False blocks updated.

## CRITICAL: Theorem FALSE for AugAssign+In/NotIn — FIX APPLIED (Session 76)

Added `bop ≠ In ∧ bop ≠ NotIn` to well_typed_stmt AugAssign definition.
ALWAYS adversarially validate with EVAL before investing in proof tactics.

### well_typed_binop boundary lemmas (2 instances: AugAssign, general)

- `well_typed_binop_not_In_second_type`: non-In/NotIn → t2≠NoneT ∧ t2≠ArrayT
- `not_NoneT_not_ArrayT`: type classification predicates → type ≠ NoneT ∧ type ≠ ArrayT

### assign_target consumers (3+ instances: Assign, AugAssign, AnnAssign)

Need 4 invariants:
1. accounts_well_typed: `metis_tac [cj 1 assign_target_preserves_accounts]`
2. state_well_typed/env_consistent: `assign_target_well_typed` (Replace) or `assign_target_well_typed_ao` (Update/any ao)
3. No-ReturnException: `drule (cj 1 assign_target_no_return) >> simp[]`
4. No-TypeError: `drule (cj 1 assign_target_no_type_error) >> simp[]` (CHEATED)

### scope_bracket consumers (3+ instances: If_True, If_False, For)

Need 3 invariants (scope_bracket_preserves now provides all 3):
1. state_well_typed
2. env_consistent
3. accounts_well_typed

Must also establish `accounts_well_typed (r with scopes...).accounts` for
the pushed state via `simp[evaluation_state_component_equality]`.

### Error characterization lemmas (X_error pattern, 8 instances)

materialise_error, assign_result_error, get_Value_error, lookup_flag_mem_error,
read_storage_slot_error, write_storage_slot_error, set_global_error,
get_immutables_error
Used via `imp_res_tac X_error >> gvs[]` for impossible INR branches.

### Key no-TypeError lemmas for well-typed expressions

- `toplevel_value_typed_no_ArrayTV_get_Value`: non-NoneTV/non-ArrayTV → get_Value ≠ INR
- `evaluate_type_not_NoneT_imp_not_NoneTV`: ty ≠ NoneT → tyv ≠ NoneTV
- `evaluate_type_BaseT_imp_not_ArrayTV`: BaseT → ¬ArrayTV
- `evaluate_type_FlagT_imp_not_ArrayTV`: FlagT → ¬ArrayTV
- `materialise_well_typed_no_type_error` (CHEATED)
- `materialise_Value_no_type_error`
- `materialise_not_HashMapRef_no_type_error`

### Monadic unfolding pattern
`simp_tac std_ss [bind_apply, BETA_THM, UNCURRY, ignore_bind_apply]`

## Skip metis_tac for goals with many assumptions
When 11+ assumptions, `metis_tac` times out. Use `irule`/`drule`.

## Build timeout: 728+ seconds needed
Full build ~728s. Interactive hol_state_at at deep blocks times out.


## CRITICAL: accounts_well_typed must be established for derived states (Session 86)

The new `accounts_well_typed st.accounts` IH antecedent means `drule_all` fails when
applying an IH to a state OTHER than `st`. Must establish `accounts_well_typed`
for the derived state BEFORE calling `drule_all`. For push_scope contexts:
`accounts_well_typed (r with scopes ...).accounts` by simp[evaluation_state_component_equality]

## CRITICAL: Missing assumptions cause drule_all failure, NOT tactic issues (Session 86)

If `drule_all` fails on an IH, the fix is almost always: establish the missing
assumption(s) that drule_all needs to discharge all IH antecedents. Don't try
qspecl_then, simp[], or other tactic variations — they just mask the real problem.
Figure out which IH antecedent is missing from assumptions and prove it first.

## CRITICAL: qspecl_then + simp[] is dangerous with multiple similar IHs (Session 86)

When both `ss` and `ss'` IHs are in assumptions, `simp[]` after qspecl_then may
incorrectly instantiate free variables from one IH using the other, producing F.
Use `drule_all` instead (which resolves antecedents from assumptions correctly).

## CRITICAL: qpat_assum (Assign block, line 1393) MUST stay as qpat_assum (Session 86)

It creates a new Q.EXISTS-wrapped assumption from the matched one. Converting to
qpat_x_assum removes the original, causing "unsolved goals: well_typed_atarget ..."
in subsequent proof steps.
