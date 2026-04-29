# LEARNINGS: Type Soundness Repair

## CRITICAL: gvs[]/fs[] Do NOT Substitute Function Application Equalities
`gvs[]`/`fs[]` only substitute variable equalities (`v = t`), NOT function applications
like `expr_type e = BaseT BoolT`. Use RULE_ASSUM_TAC:
```sml
qpat_x_assum `expr_type e = BaseT bt` (fn th =>
  RULE_ASSUM_TAC (ONCE_REWRITE_RULE[th]) >> assume_tac th)
```

## CRITICAL: imp_res_tac Silently Fails on Syntactic Mismatches
Fix: boundary lemmas with EXACT same term shape, or RULE_ASSUM_TAC to rewrite before imp_res_tac.

## CRITICAL: `by` Blocks Are Fragile in Rich Contexts
Use only for trivial subgoals (1-2 simp-closeable steps). For complex derivations, inline or extract.

## CRITICAL: Guarded IH Discharge Pattern
For guarded IHs `∀s'' tv t. guard ==> body`:
```sml
qpat_x_assum `!s'' tv t. eval_expr _ e _ = _ ==> _`
  (fn ih => mp_tac (ih |> Q.SPECL [`st`, `Value (BoolV F)`, `r`])) >>
(impl_tac >- first_assum ACCEPT_TAC) >>
disch_then drule_all >> strip_tac
```
CAUTION: Only works when specializing to a DIFFERENT expression's IH.

## CRITICAL: `>> TRY (.. >> NO_TAC)` is a BUG PATTERN (21+ instances)
After case splits, `>> TRY (tp_bind_err_tac >> NO_TAC)` silently fails if tp_bind_err_tac
can't solve the INR subgoal completely, leaving it for later tactics not designed for it.
FIX: Either (a) fix tp_bind_err_tac to handle new 4-conjunct IH conclusions, or
(b) replace with explicit `>- (INR handler)` blocks.

## CRITICAL: >> and >- have SAME precedence, left-associative
Always parenthesize after `>-`: `>- (tactic) >> rest`, NOT `>- tactic >> rest`
Same with `>-` on next line — the `>>` after closing paren needs care.

## CRITICAL: tp_bind_err_tac Doesn't Close Goals with New 4-Conjunct IH
After `drule_all >> strip_tac`, tp_bind_err_tac uses `gvs[]` to close the goal,
but gvs[] alone doesn't handle accounts_well_typed and no-TypeError conjuncts.
FIX: Add `rpt CONJ_TAC >> TRY not_return_tac >> TRY not_type_error_tac >>
TRY (first_assum ACCEPT_TAC) >> TRY (gvs[])` after the drule_all+strip_tac in tp_bind_err_tac.

## INR Error Branch Pattern (confirmed via interactive HOL session)
After `reverse (Cases_on q) >> simp_tac (srw_ss()) []`, there are 2 subgoals:
- Subgoal 1 (INR first due to reverse): error propagation case
- Subgoal 2 (INL): success path continuation
INR subgoal shape after strip_tac:
```
INR y = res ∧ st_bt = st' ⇒
  state_well_typed st' ∧ env_consistent env cx st' ∧
  accounts_well_typed st'.accounts ∧
  (∀s. res ≠ INR (Error (TypeError s))) ∧
  ∀v ret_tv. res = INR (ReturnException v) ∧ ... ⇒ value_has_type ...
```
Fix: drule_all the IH, strip_tac, then CONJ_TAC + ACCEPT for each conjunct.
Last conjunct (return-type) is vacuously true via `eval_*_not_return` + qspec_then.

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

## Tactic Anti-Patterns
- `simp[AllCaseEqs()]` on monadic bind chains → unsolvable nested existentials
- `gvs[PAIR_FST_SND_EQ]` on bind results → DESTROYS IH structure
- `rw[env_consistent_def]` → TIMEOUT (use env_consistent_scopes_only)
- `simp[evaluate_def]` without `Once` — HANGS
- `gvs[]` in rich contexts with guarded IH — TIMEOUT
- `metis_tac` with many assumptions — TIMES OUT
- `>- (tp_bind_err_tac)` when IHs have new 4-conjunct conclusions — tp_bind_err_tac incomplete
- `disch_then drule` on guarded IHs after SIMP_RULE — DISCH_THEN failure

## HOL4 Gotchas
- `optionTheory.SOME_11` (NOT `option_11`)
- `a ==> b <=> c` parses as `(a ==> b) <=> c`
- `well_typed_target_def` does NOT exist — part of `well_typed_expr_def`
- Implication theorems CANNOT be used as simp rewrites
- `imp_res_tac` silently fails on syntactic mismatches
- `>>` and `>-` have same precedence, left-associative — always parenthesize
- `gvs[]` only substitutes variable equalities, NOT function application equalities
- `>- (tactic) >>` vs `>- tactic >>` — same precedence matters in both cases
