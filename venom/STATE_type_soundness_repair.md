# STATE: Type Soundness Repair

## STRATEGIC PLAN (Session 12)

### PRIORITY 1: Fix `apply_eval_ih` SPECL exception handling

**Root cause:** `SPECL` raises `HOL_ERR` when types don't match. `first_x_assum`
treats exceptions as failure and skips to next assumption. If ALL ∀-assumptions'
SPECL calls fail, `first_x_assum` raises `FIRST_ASSUM` error — even though a
∀-assumption with a matching IH exists.

**Fix:** Wrap SPECL in exception handler so failed specializations are skipped:
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

**IMPORTANT:** If `handle UNCHANGED => NO_TAC` doesn't work with `first_x_assum`
(because UNCHANGED has special semantics in HOL4), use a different approach:
```sml
fun apply_eval_ih res_term st_term =
  ASSUM_LIST (fn ths =>
    let val ih_th = List.find (fn th =>
          is_forall (concl th) AndAlso
          length (fst (strip_forall (concl th))) >= 2) ths
    in case ih_th of
         SOME th => let val vars = fst (strip_forall (concl th))
                        val n = length vars
                        val front = List.take (vars, n-2)
                    in mp_tac (SPECL (front @ [res_term, st_term]) th) end
       | NONE => NO_TAC
    end) >>
  simp_tac (srw_ss()) [] >> strip_tac
```

**Verification:** After fixing, test on Raise3 first (simplest failing block with IH application).

### PRIORITY 2: Cheat all failing blocks, then inspect each with hol_state_at

After Priority 1, if some blocks still fail:
1. Temporarily `cheat` all blocks that use `apply_eval_ih` / `close_inr_err_tac` / `tp_bind_err_tac`
2. Build to verify the skeleton compiles with all cheats
3. Replace one cheat at a time, use `hol_state_at` to inspect REAL proof state
4. Fix the tactic based on what's actually in the assumptions

### PRIORITY 3: Fix `drule_all` calls in blocks like Assert3

Assert3 at line 1141 uses `first_x_assum drule_all` which may not resolve
`accounts_well_typed st.accounts` from assumptions. Fix: replace with
`apply_eval_ih` or use `qpat_x_assum 'accounts_well_typed _' assume_tac`
before `drule_all`.

### PRIORITY 4: Prove 6 cheats in helpers file

## EVAL RETURN TYPES (VERIFIED Session 11)
- eval_stmt: `(unit + exception) # evaluation_state`
- eval_expr: `(toplevel_value + exception) # evaluation_state`
- eval_stmts: `(unit + exception) # evaluation_state`
- eval_iterator: `(value list + exception) # evaluation_state`
- eval_target: `(assignment_value + exception) # evaluation_state`
- eval_targets: `(assignment_value list + exception) # evaluation_state`
- eval_base_target: `((location # subscript list) + exception) # evaluation_state`

## IH VARIABLE COUNTS
- eval_expr (P7): 4 vars ∀env st res st'
- eval_stmt (P0): 5 vars ∀env ret_ty st res st'
- eval_stmts (P1): 5 vars ∀env ret_ty st res st'
- eval_iterator (P2): 4 vars ∀env typ st res st' (2nd var is `typ`)
- eval_target (P3): 4 vars ∀env st res st'
- eval_targets (P4): 4 vars ∀env st res st'
- eval_base_target (P5): 4 vars ∀env st res st'
- eval_for (P6): 7 vars ∀env typ ret_ty st res st'
- eval_exprs (P8): 4 vars ∀env st res st'

## BLOCK STATUS (from holmake output, Session 11)

### PROVED (26 blocks — need re-verification after tactic changes):
Pass, Continue, Break, ReturnNone, ReturnSome, Raise1, Raise2, Assert1, Assert2,
Assert3, Log, Expr, stmts_nil, stmts_cons, BaseTarget, TupleTarget,
targets_nil, targets_cons, NameTarget, BareGlobalNameTarget,
TopLevelNameTarget, AttributeTarget, for_nil, Name, Literal, exprs_nil

### FAILING (Raise3 first, then cascading):
Raise3: FIRST_ASSUM error in apply_eval_ih (SPECL exception bug)
Assert3: Cases_on `b` fails (after cheating Raise3) - drule_all doesn't resolve
accounts_well_typed; the IH application produces no ∃b assumption so b is undefined
All other blocks described as "failing" in previous STATEs: untested since
they're blocked by earlier block failures in the holmake process

### CHEATS (6 in helpers file):
| Theorem | What |
|---------|------|
| env_consistent_pop_scope | Pop scope preserves env_consistent |
| env_consistent_preserves_tv | Eval preserves tv+env_consistent |
| bind_arguments_env_consistent | Call arg binding preserves env |
| set_immutable_well_typed | set_immutable preserves typing |
| assign_target_well_typed | Assignment replace preserves typing |
| eval_expr_not_HashMapRef | Well-typed eval not HashMapRef |

## WHAT NOT TO TRY
- `qpat_x_assum` with complex ∀-variable patterns — FAILS after IH instantiation
- `qspecl_then` with untyped backtick terms — FAILS (wrong types at SML load time)
- `>|` (THENL) in Resume blocks — returns gentactic, not tactic
- `>-` / THEN1 in Resume blocks — SML type error (gentactic vs tactic)
- `first_x_assum drule_all` — HANGS in rich IH contexts
- `simp[evaluate_def]` without `Once` — HANGS
- `metis_tac` with many assumptions — TIMES OUT
- Missing `>>` between consecutive tactic lines — SML type error
- Guessing at proof state instead of using hol_state_at — WASTES TIME
- Holmake-only debugging (16-45s per cycle) — TOO SLOW for iteration
- SPECL without exception handling in first_x_assum — SPECL failure kills search

## RISK ASSESSMENT
- HIGH: apply_eval_ih SPECL exception handling — ALL blocks using IH depend on this
- MEDIUM: drule_all in blocks like Assert3 — may need switch to apply_eval_ih
- MEDIUM: Different state variable names across blocks (r, st_tgt, st1, etc.)
- LOW: Individual block logic after IH application works

## KEY FILES
- Main theorem: semantics/prop/vyperTypeSoundnessScript.sml (~4029 LOC on disk, original)
- Helpers: semantics/prop/vyperTypeSoundnessHelpersScript.sml (~7307 LOC, 6 cheats)
- Workdir: semantics/prop/
