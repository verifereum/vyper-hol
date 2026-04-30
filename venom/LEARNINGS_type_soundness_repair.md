# LEARNINGS: Type Soundness Repair

## gvs[] Auto-Applies IHs (Session 28 KEY discovery)

### `Cases_on q >> gvs[]` handles everything
After `Cases_on `q` >> gvs[]` (no extra rewrites), the augmented simpset:
1. **Auto-solves INR error cases** via exception_distinct + error_distinct
2. **Auto-applies IHs** for the INL case via assumption resolution (if ∃-witness exists)
3. **Adds IH conclusions** as assumptions: state_well_typed, env_consistent, accounts_well_typed

### NEVER use `first_x_assum drule_all` after gvs[] — the IH is ALREADY consumed
This is the #1 failure pattern across sessions 26-28. Symptoms: FIRST_ASSAM error,
"no suitable assumption", or wrong IH consumed.

### CORRECT monadic case split pattern (replaces ALL previous):
```sml
Cases_on `eval_X cx arg st` >>
Cases_on `q` >> gvs[] >>
(* gvs[] auto-solves INR + applies IH for INL case *)
(* Add ONLY what gvs[] can't handle *)
```

### GUARDED IH: needs explicit qspecl_then (2+ blocks)
gvs[] can't match guarded IH antecedents with pair destructuring:
```sml
qpat_x_assum `!s'' loc sbs t'. eval_base_target _ _ _ = _ ==> _`
  (qspecl_then [`st`, `FST x'`, `SND x'`, `st_bt`] mp_tac) >>
(impl_tac >- first_assum ACCEPT_TAC) >> strip_tac
```

### Q.EXISTS for ∃-witness (3 blocks: Assign, AugAssign, Append)
```sml
qpat_assum `well_typed_target env bt _`
  (fn th => ASSUME_TAC (Q.EXISTS (`?ty'. well_typed_target env bt ty'`,
                                  `ArrayT (expr_type e) bd`) th))
```

## Quotation Syntax

### NO Unicode in qpat_x_assum quotations
`∃`, `∧`, `⇒`, `∀` cause Q_TAC0 parse errors. Use ASCII: `?`, `/\`, `==>`, `!`

### Parenthesize existentials
`?ty. P ty /\ _` parses as `?ty. (P ty /\ _)`. Need `(?ty. P ty) /\ _`.

## SML Type System in Resume Blocks

- `>- tac1 >- tac2` → SML type error (gentactic mismatch)
- `>- suspend` → type error (suspend creates subgoal)
- `apply_eval_ih` returns gentactic → cannot compose with `>>`
- Use `>>` between steps, `>-` only when solving exactly one subgoal

## State Preservation Lemmas (10+ uses)
All pure ops: `st' = st`. Use: `imp_res_tac X_state >> gvs[]`
- materialise_state, get_Value_state, lift_option_type_state
- lift_option_state, lift_sum_state, check_state
- type_check_state, switch_BoolV_state

## Key Boundary Lemmas

### In vyperTypeSoundnessHelpersScript.sml (308 theorems):
- append_chain_decompose, assign_target_well_typed_ao
- assign_subscripts_append_dynamic, materialise_no_type_error
- evaluate_type_NoneTV_imp_NoneT

### In main file (lines 217-233):
- evaluate_type_BaseT_inv, toplevel_value_typed_for_BaseT
- toplevel_value_typed_BoolT_inv, value_has_type_BoolT_inv

### In vyperBuiltinTyping:
- evaluate_builtin_well_typed: all builtin operations preserve typing

## Variable Naming
gvs[] changes variable structure. NEVER assume names.
Always use `rename1` after gvs/cases to re-establish expected names.

## Testing Discipline
- Test after EACH rewrite, not after 3
- hol_check_proof does NOT verify Resume blocks; only holmake does
- Call plan_oracle after 2-3 failed attempts, not 15+

## AVOID
- `first_x_assum drule_all` after gvs[] — IH already consumed
- `apply_eval_ih` in Resume blocks — type error (gentactic)
- Unicode in qpat_x_assum quotations — Q_TAC0
- `>- (close_inr_err_tac ...)` when augmented ss may solve INR
- `Cases_on v` where `v : value` → TIMEOUT
- `simp[AllCaseEqs()]` on monadic bind chains → TIMEOUT
- `>- suspend` — suspend creates a subgoal, doesn't solve one
- Making 5+ edits without testing after each

## Gentactic Bug: close_inr_err_tac / apply_eval_ih (Session 29)

### `apply_eval_ih` returns gentactic → CANNOT compose with >> in Resume blocks
This breaks `close_inr_err_tac` and `close_inr_err_tac_for`.
Affects: Assign, AugAssign, any block using `TRY close_inr_err_tac`.
Fix: Replace with explicit drule + qspecl_then IH application.

### Pattern for INR case in monadic bind proofs (replaces close_inr_err_tac):
```sml
Cases_on `res` >> simp_tac (srw_ss()) [] >-
(* INR case - terminal, can use gvs *)
(strip_tac >> gvs[] >>
 first_x_assum drule >> strip_tac >>
 rpt CONJ_TAC >> TRY (first_assum ACCEPT_TAC) >>
 rpt strip_tac >> not_type_error_tac) >>
(* INL case continues *)
```

## qpat_x_assum Constraints

### NO wildcards `_` in qpat_x_assum patterns
`\`!env st res st'. (?ty. _) /\ _ ==> _\`` → Q_TAC0 ERROR
Use concrete patterns matching your assumption, or use drule/drule_all.

### NO Unicode (∃∧⇒∀) in qpat_x_assum → Q_TAC0 ERROR
Use ASCII: ?, /\, ==>, !

## Incremental Construction (CRITICAL)

Writing 5+ tactic lines without verifying is the #1 failure pattern.
After EACH tactic, use hol_state_at to verify the goal state matches
expectations. If variables don't match, rename/fix BEFORE continuing.
This is NOT optional - it's the difference between 1-pass success and
6-attempt failure.
