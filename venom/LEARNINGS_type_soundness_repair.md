# LEARNINGS: Type Soundness Repair

## drule_at (Pos last) vs drule — CRITICAL FIX (Session 3)
`first_x_assum drule` matches the FIRST antecedent of an implication.
For IHs like `∀env st res st'. well_typed_X ∧ ... ∧ eval_X ... = (res,st') ⇒ Q`,
drule matches `well_typed_X` which has many matches → combinatorial explosion.
`first_x_assum (drule_at (Pos last))` matches the LAST antecedent (`eval_X`),
which is unique per IH → O(1) matching. Build goes from 1800s timeout to 155s.
**CAVEAT:** Cannot blindly replace drule→drule_at(Pos last) inside multipurpose
tactics like tp_bind_err_tac because it changes which IHs succeed in which cases,
altering the assumption context for subsequent proof steps. Must split into
separate INR and INL tactics.

## drule_all/drule in rich contexts: HANGS (confirmed Sessions 2-3)
`first_x_assum drule_all` or `first_x_assum drule` on goals with 10+ IH assumptions
(each with 7+ antecedents) causes combinatorial explosion. Root cause: `first_x_assum`
iterates ALL assumptions trying to match, and `drule` matches FIRST antecedent.

## tp_bind_err_tac design flaw: conflation of INR and INL (Session 3)
tp_bind_err_tac tries to handle both INR error propagation and INL success
continuation in one tactic with fallthrough strategies. This means:
- `drule` matching changes break fallthrough behavior
- `TRY (tp_bind_err_tac >> NO_TAC)` silently fails when INR isn't fully closed
- Context from partial IH matches in INR case pollutes INL case
**Fix:** Split into `close_inr_err_tac` (complete INR closing) and `tp_inl_tac`
(IH + state resolution for INL continuation).

## Build -j8 parallelism masks individual block failures (Sessions 2-3)
With Holmake parallelism, simple blocks prove on other workers while blocks
using tp_bind_err_tac hang. "26 blocks proved" doesn't mean those proofs are
correct — just means they avoid the hanging tactic. Assert3 was listed as proved
but fails in -j1 build.

## TRY + NO_TAC silently fails on INR cases (Sessions 1-3)
`TRY (tp_bind_err_tac >> NO_TAC)` after a case split: if tp_bind_err_tac can't solve
the INR subgoal, TRY silently swallows the failure. The INR subgoal remains for
the NEXT tactic (designed for INL success case), which fails confusingly.

## CRITICAL: gvs[]/fs[] Do NOT Substitute Function Application Equalities
`gvs[]`/`fs[]` only substitute variable equalities (`v = t`), NOT function applications
like `expr_type e = BaseT BoolT`. Use RULE_ASSUM_TAC:
```sml
qpat_x_assum `expr_type e = BaseT bt` (fn th =>
  RULE_ASSUM_TAC (ONCE_REWRITE_RULE[th]) >> assume_tac th)
```

## CRITICAL: imp_res_tac Silently Fails on Syntactic Mismatches
Fix: boundary lemmas with EXACT same term shape, or RULE_ASSUM_TAC to rewrite.

## CRITICAL: >> and >- have SAME precedence, left-associative
Always parenthesize after `>-`: `>- (tactic) >> rest`, NOT `>- tactic >> rest`

## materialise chain (7 lemmas, used in 3+ blocks)
- materialise_no_type_error, materialise_type_error_NoneTV
- materialise_type_error_imp_HashMapRef
- materialise_Value_no_type_error, materialise_well_typed_no_type_error
- materialise_not_HashMapRef_no_type_error
Key: materialise TypeError → is_HashMapRef → tyv = NoneTV → NoneT → well_typed excludes NoneT

## toplevel_value classification (5 lemmas, used in 13+ blocks)
- evaluate_type_BaseT_inv: `evaluate_type tenv (BaseT bt) = SOME tv ==> tv = BaseTV bt`
- toplevel_value_typed_BoolT_inv: BEST for BoolT
- evaluate_type_not_NoneT_imp_not_NoneTV
- evaluate_type_BaseT_imp_not_ArrayTV
- is_HashMapRef_toplevel_value_typed_NoneTV

## evaluate_builtin_well_typed (1 lemma, FULLY PROVED)
In vyperBuiltinTypingScript.sml. Takes `accounts_well_typed acc` precondition.
Covers ALL builtin cases including MakeArray, Acc, Convert, AbiEncode.

## drule_at (Pos last) usage pattern (HOL4)
- `drule_at : match_position -> thm_tactic` (from Tactic.sig)
- `match_position = Any | Pat of quotation | Pos of (term list -> term) | Concl`
- `Pos last` matches the LAST antecedent of an implication
- `dxrule_at (Pos last)` also REMOVES the matched assumption (useful for INR closing)
- Use for any IH application where the LAST antecedent is unique (e.g., eval equality)

## Tactic Anti-Patterns
- `simp[AllCaseEqs()]` on monadic bind chains → unsolvable nested existentials
- `gvs[PAIR_FST_SND_EQ]` on bind results → DESTROYS IH structure
- `rw[env_consistent_def]` → TIMEOUT (use env_consistent_scopes_only)
- `simp[evaluate_def]` without `Once` — HANGS
- `gvs[]` in rich contexts with guarded IH — TIMEOUT
- `metis_tac` with many assumptions — TIMES OUT
- `disch_then drule` on guarded IHs after SIMP_RULE — DISCH_THEN failure
- `imp_res_tac` before IH application — ADDS CLUTTER


## close_inr_err_tac: IH variable capture (Session 4)
After `dxrule_at (Pos last)`, the IH's universally quantified variables
(`env`, `st`) get renamed by HOL4 to avoid capture (e.g., `env'`, `st'`).
These renamed variables don't match the original assumptions (`env`, `st`).
`ACCEPT_TAC` fails because `well_typed_expr env' e` ≠ `well_typed_expr env e`.
FIX: Use `gvs[]` which does variable elimination, or use `drule_all` which
resolves all antecedents at once.

## close_inr_err_tac: Missing no-return resolution (Session 4)
The P7 (eval_expr) IH conclusion includes `∀s. res ≠ INR (Error (TypeError s))`
but NOT the `∀v ret_tv. res = INR (ReturnException v) ⇒ ...` conjunct.
That conjunct requires `eval_X_not_return` + constructor distinctness.
FIX: After IH application, add `not_return_tac` or `imp_res_tac eval_expr_not_return >> simp_tac`.

## SML operator precedence: >> and >- (Session 4)
`>>` and `>-` have the SAME precedence and are LEFT-ASSOCIATIVE.
So `simp_tac [] >- (close_inr_err_tac) >> rest` parses as
`((simp_tac [] >- close_inr_err_tac) >> rest)` but the type of `>-` result
is `gentactic` not `tactic`, causing type mismatch with `>>`.
FIX: Use `TRY (close_inr_err_tac >> NO_TAC) >>` instead of `>- (close_inr_err_tac) >>`.
Or parenthesize: `(simp_tac [] >> (>- close_inr_err_tac)) >> rest` (less readable).

## dxrule_at vs drule_at for INR closing (Session 4)
`dxrule_at (Pos last)` removes the matched assumption, which is desirable
for INR closing (removes the eval_equality to prevent re-matching). But
the resulting IH antecedents may have renamed variables. `drule_at (Pos last)`
keeps the assumption but has the same variable capture issue.
