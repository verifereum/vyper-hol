# STATE: Type Soundness Repair

## CRITICAL CONTEXT (read first)

**Build fails at Raise3 (line 870)** because `close_inr_err_tac` doesn't close INR subgoals. Leaves 5 residual subgoals.

**Root cause (two parts):**
1. **Variable capture after dxrule_at**: IH's `∀env st` become `env'`, `st'` after instantiation, not matching assumptions `env`, `st`. `ACCEPT_TAC` fails.
2. **Missing no-return resolution**: IH (P7 eval_expr) conclusion has `∀s. res ≠ INR (Error (TypeError s))` but NOT `∀v ret_tv. res = INR (ReturnException v) ⇒ ...`. That needs `eval_X_not_return` + constructor distinctness.

**Historical note**: The old `tp_bind_err_tac` (with plain `drule`) NEVER handled INR cases — those 29 blocks all hung. With `drule_at (Pos last)`, it partially handles INR but doesn't finish. Both versions are broken; the fix needs to work from scratch.

## FIX PLAN (next session)

### Step 1: Examine the 5 residual goals (5 min)

In interactive HOL, apply close_inr_err_tac to the INR goal and inspect the 5 remaining goals. This tells us exactly what's missing.

### Step 2: Fix close_inr_err_tac (20 min)

Two options, ranked by likelihood of success:

**Option A: Use gvs[] instead of simp_tac + ACCEPT_TAC**
```sml
val close_inr_err_tac : tactic =
  strip_tac >>
  TRY (POP_ASSUM STRIP_ASSUME_TAC) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  first_x_assum (dxrule_at (Pos last)) >>
  rpt strip_tac >>
  gvs[] >>
  TRY not_return_tac >>
  TRY not_type_error_tac >>
  simp_tac (srw_ss()) [];
```
`gvs[]` does variable elimination which might unify `env'` with `env`. Then `not_return_tac` handles the no-return conjunct.

**Option B: Use drule_all instead of drule_at (Pos last)**
```sml
val close_inr_err_tac : tactic =
  strip_tac >>
  TRY (POP_ASSUM STRIP_ASSUME_TAC) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  (* Try ALL IH antecedents at once *)
  first_x_assum drule_all >>
  rpt strip_tac >>
  TRY not_return_tac >>
  TRY not_type_error_tac >>
  simp_tac (srw_ss()) [];
```
`drule_all` resolves ALL antecedents from assumptions but was reported slow in general contexts. For INR cases (where all antecedents ARE present), it should be fast because there's a unique match.

**Option C: Completely different — reorder tp_bind_err_tac strategies**
Put eval_X_not_return constructors FIRST in tp_bind_err_tac (with NO_TAC), so INR cases close before IH application is attempted. BUT: must also handle state preservation, which needs IH. So this alone isn't sufficient.

**Most likely fix**: Option A (gvs[] + not_return_tac + not_type_error_tac). Try this first.

### Step 3: Test on a simple block (5 min)

Test close_inr_err_tac on the INR subgoal in Raise3. If it closes, proceed to full build.

### Step 4: Full build (5 min)

If close_inr_err_tac works for Raise3, build full theory. Expect some blocks may need individual fixes for unusual INR shapes.

### Step 5: Prove the 6 cheat lemmas in helpers file

After all INR fixes are stable:
- env_consistent_pop_scope
- env_consistent_preserves_tv
- bind_arguments_env_consistent
- set_immutable_well_typed
- assign_target_well_typed
- eval_expr_not_HashMapRef

## CURRENT FILE STATE

The file has `close_inr_err_tac` and `close_pure_inr_err_tac` defined (lines ~793-809), and 23 call sites using them via `TRY (... >> NO_TAC)`. The old `tp_bind_err_tac` is still present for the 4 remaining uses (Raise3/Assert3 end-of-block, evaluate_attribute, exprs_cons).

Current definitions:
```sml
val close_inr_err_tac : tactic =
  strip_tac >>
  TRY (POP_ASSUM STRIP_ASSUME_TAC) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  TRY (first_x_assum (dxrule_at (Pos last))) >>
  rpt strip_tac >>
  TRY (rpt (first_assum ACCEPT_TAC)) >>
  simp_tac (srw_ss()) [];

val close_pure_inr_err_tac : tactic =
  strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  rpt CONJ_TAC >> TRY (first_assum ACCEPT_TAC) >>
  rpt strip_tac >> simp_tac (srw_ss()) [];
```

These are BROKEN — must be fixed before build succeeds.

## EXISTING TACTICS IN FILE

| Tactic | Line | Purpose | Status |
|--------|------|---------|--------|
| not_return_tac | ~185 | Discharge "not ReturnException" | Works |
| not_type_error_tac | ~248 | Discharge "not TypeError" | Works |
| close_impossible_branch_tac | ~300 | Close F goals | Works |
| tp_err_tac | ~313 | Full error branch: state resolve + CONJ | Works (Subscript) |
| tp_pure_err_tac | ~334 | Pure error branch | UNUSED |
| tp_materialise_conclusion_tac | ~339 | Simplify materialise IH conclusion | Works |
| discharge_ih_tac | ~380 | Targeted MATCH_MP IH application | UNUSED |
| tp_stmt_no_return_tac | ~409 | Simple stmt cases | Works |
| tp_bind_err_tac | ~815 | Generic error+success handler | **Still broken for INR** |
| close_inr_err_tac | ~793 | Close INR error branch | **BROKEN — needs fix** |
| close_pure_inr_err_tac | ~805 | Close pure INR branch | Untested |

## BLOCK STATUS

### PROVED (26+ blocks):
Pass, Continue, Break, ReturnNone, ReturnSome, Raise1, Raise2, Assert1, Assert2,
Assert3**, Log, Expr, stmts_nil, stmts_cons, BaseTarget, TupleTarget,
targets_nil, targets_cons, NameTarget, BareGlobalNameTarget,
TopLevelNameTarget, AttributeTarget, for_nil, Name, Literal, exprs_nil

** Assert3: might need fixing after close_inr_err_tac repaired

### FAILING (blocks using close_inr_err_tac that currently fail):
AnnAssign, Append, Array, Assign, Attribute, AugAssign,
BareGlobalName, Builtin, CreateTarget, ExtCall, FlagMember, For, If, IfExp,
IntCall, Pop, Range, RawCallTarget, RawLog, RawRevert, SelfDestructTarget,
Send, StructLit, Subscript, SubscriptTarget, TopLevelName, TypeBuiltin,
exprs_cons, for_cons

### CHEATS (6 in helpers file):
env_consistent_pop_scope, env_consistent_preserves_tv, bind_arguments_env_consistent,
set_immutable_well_typed, assign_target_well_typed, eval_expr_not_HashMapRef

## CALL SITE CATEGORIZATION

### Standard eval_X INR → close_inr_err_tac (NEEDS FIX):
Lines ~863, 1036, 1132, 1156, 1209, 1342, 1420, 1495, 1821, 1829, 2047, 2183, 2307, 2680, 2738, 3747, 3758

### Pure op INR → close_pure_inr_err_tac (UNTESTED):
Lines ~1444 (Cases_on x/toplevel_value), 1954 (get_immutables), 1960 (FLOOKUP), 2311 (get_Value), 3753 (materialise)

### End-of-block tp_bind_err_tac (keep as-is):
Lines ~887 (Raise3), ~1185 (Assert3), ~2316 (evaluate_attribute), ~3766 (exprs_cons return)

## SML SYNTAX WARNING

**`>- (close_inr_err_tac) >>` causes TYPE ERROR!** `>>` and `>-` have same precedence, left-associative. Must use `TRY (close_inr_err_tac >> NO_TAC) >>` instead.

## WHAT NOT TO TRY
- `>- (close_inr_err_tac) >>` — SML type error (precedence)
- `first_x_assum drule_all` or `first_x_assum drule` in tp_bind_err_tac — HANGS
- `>> TRY (.. >> NO_TAC)` for INR when close doesn't close fully — silently fails
- `simp[evaluate_def]` without `Once` — HANGS
- `gvs[]` to substitute `expr_type e = BaseT bt` — DOESN'T WORK
- `metis_tac` with many assumptions — TIMES OUT
- Any approach that doesn't handle BOTH IH application AND not_return in INR cases

## KEY FILES
- Main theorem: semantics/prop/vyperTypeSoundnessScript.sml (~4021 LOC)
- Helpers: semantics/prop/vyperTypeSoundnessHelpersScript.sml (~7307 LOC, 6 cheats)
- Workdir: semantics/prop/
- Build command: holmake(workdir="semantics/prop", target="vyperTypeSoundnessTheory", timeout=600)
