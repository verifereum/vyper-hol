# LEARNINGS: Type Soundness Repair

## SPECL exception handling in tactic combinators (Sessions 9-11)

**CRITICAL:** When using `first_x_assum (fn th => ... SPECL [...] th ...)` inside
ML tactic functions, SPECL raises `HOL_ERR` when types don't match. `first_x_assum`
treats ANY exception from the predicate function as failure and skips to next
assumption. If ALL ∀-assumptions' SPECL calls fail, `first_x_assum` raises
FIRST_ASSUM error — even though a ∀-assumption exists.

**Fix:** Wrap SPECL in exception handler:
```sml
val spec_th = SPECL (front @ [res_term, st_term]) th
     handle HOL_ERR _ => raise UNCHANGED
```
This causes failed specializations to be silently skipped, allowing `first_x_assum`
to try the next ∀-assumption.

**Alternative:** Use `every_assum` instead of `first_x_assum` to try ALL assumptions.
Or use `ASSUM_LIST` to filter ∀-assumptions explicitly.

## first_x_assum + is_forall + SPECL: IH application approach (Sessions 7-11)

**The fundamental IH application fix.** All approaches based on `qpat_x_assum`
with named ∀-variables or `qspecl_then` with untyped backtick terms FAIL because:
- `qpat_x_assum` can't match IHs due to HOL4 ∀-variable patterns
- `qspecl_then` backtick terms lack type annotations → wrong types in SML context
- `dxrule_at (Pos last)` + `strip_tac` has variable capture for remaining ∀-vars

**Working pattern (verified in Raise3 interactive test):**
```sml
first_x_assum (fn th =>
  if is_forall (concl th) then
    mp_tac (SPECL [``env:typing_env``,``st:evaluation_state``,
      ``INR y:(toplevel_value + exception)``,``r:evaluation_state``] th)
  else NO_TAC) >>
simp_tac (srw_ss()) [] >> strip_tac >> gvs[]
```
**CRITICAL:** Type annotations on ALL backtick terms are required. Without them,
type inference at SML load time gets wrong types, causing NO_TAC to fire for all
assumptions → FIRST_ASSUM error.

**Robust version using IH bound variables for first n-2 args (NEEDS SPECL exception handling):**
```sml
fun apply_eval_ih res_term st_term =
  first_x_assum (fn th =>
    if is_forall (concl th) then
      let val vars = fst (strip_forall (concl th))
          val n = length vars
      in if n >= 2 then
           let val front = List.take (vars, n-2)
               val spec_th = SPECL (front @ [res_term, st_term]) th
                    handle HOL_ERR _ => raise UNCHANGED
           in mp_tac spec_th end
         else NO_TAC
      end handle UNCHANGED => NO_TAC
    else NO_TAC) >>
  simp_tac (srw_ss()) [] >> strip_tac
```

∀-var count per eval function (for SPECL args):
- eval_expr: 4 (env, st, res, st')
- eval_stmt: 5 (env, ret_ty, st, res, st')
- eval_stmts: 5 (env, ret_ty, st, res, st')
- eval_iterator: 4 (env, [typ], st, res, st') — NOTE: 2nd var may be `typ` not `st`
- eval_target: 4 (env, st, res, st')
- eval_targets: 4 (env, st, res, st')
- eval_base_target: 4 (env, st, res, st')
- eval_for: 7 (env, typ, ret_ty, st, res, st')

## Eval function return types (VERIFIED Session 11)
- eval_stmt: `unit + exception`
- eval_stmts: `unit + exception`
- eval_expr: `toplevel_value + exception`
- eval_iterator: `value list + exception`
- eval_target: `assignment_value + exception`
- eval_targets: `assignment_value list + exception`
- eval_base_target: `(location # subscript list) + exception`

## Cases_on pair destructuring: q = result, r = state
After `Cases_on \`eval_expr cx e st\``, HOL4 names:
- `q` = result component (the eval result, e.g., `toplevel_value + exception`)
- `r` = new state (`evaluation_state`)
Then `Cases_on \`q\`` gives INL `x` (success) / INR `y` (error, `y:exception`)
After this split, use `TRY (INR_tac >> NO_TAC) >> INL_tac` for subgoal management.

## INR/INL subgoal management in Resume blocks
`>-` and `>|` produce gentactic, NOT tactic — cannot use in Resume blocks.
Working pattern: `TRY (close_inr_err_tac >> NO_TAC) >> inl_case_tac`
TRY makes it safe: if current subgoal is INL, INR tactic fails, TRY drops it.

## toplevel_value_typed_for_BaseT: KEY boundary lemma
`∀tenv bt tv. evaluate_type tenv (BaseT bt) = SOME tyv ∧ toplevel_value_typed tv tyv ⇒ ∃v. tv = Value v`
After `imp_res_tac`, use `gvs[toplevel_value_typed_def]` to resolve constructor equality.

## AllCaseEqs() replaces manual Cases_on for option/bool
`simp_tac (srw_ss()) [..., AllCaseEqs()]` eliminates `case dest_XV v of NONE => ... | SOME x => ...`
without needing explicit `Cases_on`.

## State lemmas for pure operations (used 10+ times)
- materialise_state, get_Value_state, lift_option_type_state, lift_option_state
- lift_sum_state, check_state, type_check_state, return_state, raise_state
- switch_BoolV_state, handle_loop_exception_state
All prove `st' = st` (state unchanged on success or error).
Use: `imp_res_tac X_state >> gvs[]`

## drule_all in rich IH contexts: MAY HANG or resolve incorrectly (Sessions 2-3, 11)
The new IH has `accounts_well_typed st.accounts` as an additional antecedent.
`drule_all` must find this in assumptions. If it picks the wrong assumption or
can't find it, the IH application fails silently or hangs.
Prefer `apply_eval_ih` for IH application.

## CRITICAL: gvs[]/fs[] Do NOT Substitute Function Application Equalities
Use RULE_ASSUM_TAC with ONCE_REWRITE_RULE instead.

## CRITICAL: >> and >- have SAME precedence, left-associative
Always parenthesize after `>-` in Resume blocks.

## Tactic Anti-Patterns
- `simp[AllCaseEqs()]` on monadic bind chains → unsolvable nested existentials
- `gvs[PAIR_FST_SND_EQ]` on bind results → DESTROYS IH structure
- `rw[env_consistent_def]` → TIMEOUT (use env_consistent_scopes_only)
- `simp[evaluate_def]` without `Once` — HANGS
- `metis_tac` with many assumptions — TIMES OUT
- `imp_res_tac` before IH application — ADDS CLUTTER

## materialise chain (7 lemmas, used in 3+ blocks)
Key: materialise TypeError → is_HashMapRef → tyv = NoneTV → NoneT → well_typed excludes NoneT

## toplevel_value classification (5 lemmas, used in 13+ blocks)
- evaluate_type_BaseT_inv, toplevel_value_typed_BoolT_inv
- evaluate_type_not_NoneT_imp_not_NoneTV, evaluate_type_BaseT_imp_not_ArrayTV
- is_HashMapRef_toplevel_value_typed_NoneTV

## evaluate_builtin_well_typed (1 lemma, FULLY PROVED)
Takes `accounts_well_typed acc` precondition. Covers ALL builtin cases.

## >- / THEN1 produces gentactic, NOT tactic, in Resume blocks
Workarounds: `TRY (tac >> NO_TAC)`, or structured proof with separate subgoals.
`>|` (THENL) also returns gentactic — cannot use in Resume blocks either.

## augment_srw_ss makes constructor distinctness trivial
`augment_srw_ss[rewrites [exception_distinct, error_distinct]]` proves
`INR y ≠ INR (Error (TypeError s))` etc. automatically via simp[].

## Debugging workflow (Session 11)
NEVER rely solely on holmake for debugging (16-45s/cycle). USE hol_state_at:
1. Cheat all failing blocks to get build past them
2. Use hol_state_at on each failing block to inspect REAL proof state
3. Design fix based on REAL assumptions, not guessing
4. One holmake to verify
