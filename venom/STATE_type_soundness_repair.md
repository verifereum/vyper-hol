# STATE: Type Soundness Repair

## CRITICAL CONTEXT (read first)

Build fails at Append block. Root cause: `tp_bind_err_tac` doesn't close INR
error-propagation subgoals after IH conclusion was strengthened to 4 conjuncts
(+accounts_well_typed, +no-TypeError). The tactic uses `drule_all >> strip_tac >>
gvs[]` but gvs[] alone can't handle the new conjuncts. This affects 21+
`TRY (tp_bind_err_tac >> NO_TAC)` instances across all 29 remaining blocks.

## STRATEGIC PLAN (next session)

### Step 1: Fix tp_bind_err_tac (HIGH PRIORITY, 15 min)
File: `semantics/prop/vyperTypeSoundnessScript.sml`, line 785

The tactic (line 800) has:
```sml
TRY (first_x_assum drule_all >> strip_tac >>
     imp_res_tac eval_expr_not_return >>
     ... [more not_return] ...
     imp_res_tac materialise_error >>
     gvs[]) >>
```

After `drule_all >> strip_tac`, the IH gives us the 4 conjuncts as assumptions.
The `gvs[]` may not close the goal because:
1. The no-TypeError conjunct `∀s. res ≠ INR (Error (TypeError s))` might not
   simplify directly from the IH (it's there as an assumption but the goal
   might need ACCEPT_TAC or a different form).
2. The accounts_well_typed conjunct may need explicit handling.

**PROPOSED FIX**: After the `gvs[]` in the first TRY branch, add:
```sml
rpt CONJ_TAC >>
TRY not_return_tac >>
TRY not_type_error_tac >>
TRY (first_assum ACCEPT_TAC) >>
TRY (gvs[])
```

If this doesn't work, try adding it BEFORE gvs[] since gvs might change the goal shape.

ALTERNATIVE: The issue might be simpler — after `drule_all >> strip_tac`,
the conclusions from the IH are added as assumptions, and the GOAL still has
conjuncts. So we need `rpt CONJ_TAC` to split them, then each subgoal should
be solvable by ACCEPT_TAC (matching the assumption from IH) or not_return_tac
(for the "not a ReturnException" subgoal via eval_*_not_return lemmas).

### Step 2: Build and iterate (30 min)
After fixing tp_bind_err_tac, run holmake. If it passes Append, continue to
next failures. Each remaining block should compile if tp_bind_err_tac works.

### Step 3: If tp_bind_err_tac fix doesn't work for specific blocks
Some blocks use guarded IHs that require `qspecl_then` + `impl_tac` instead
of simple `drule_all`. For these, the `>-` approach is needed:
```sml
reverse (Cases_on `q`) >> simp_tac (srw_ss()) [] >-
  (strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
   qpat_x_assum `!env st res st'. ... eval_X _ _ _ = _ ==> _`
     (qspecl_then [`env`, `st`, `INR y`, `st_bt`] mp_tac) >>
   (impl_tac >- (rpt CONJ_TAC >> first_assum ACCEPT_TAC)) >>
   strip_tac >>
   rpt CONJ_TAC >> TRY (first_assum ACCEPT_TAC) >>
   rpt strip_tac >> gvs[] >>
   imp_res_tac eval_X_not_return >>
   first_x_assum (qspec_then `v` mp_tac) >> simp_tac (srw_ss()) [])
```

### Step 4: Prove cheat lemmas when blocking (6 cheats in helpers file)

## BLOCK STATUS

### PROVED (26 blocks):
Pass, Continue, Break, ReturnNone, ReturnSome, Raise1, Raise2, Raise3,
Assert1, Assert2, Assert3, Log, Expr, stmts_nil, stmts_cons, BaseTarget,
TupleTarget, targets_nil, targets_cons, NameTarget, BareGlobalNameTarget,
TopLevelNameTarget, AttributeTarget, for_nil, Name, Literal, exprs_nil

### FAILING (29 blocks — first failure stops build):
AnnAssign, Append (FIRST), Array, Assign, Attribute, AugAssign, BareGlobalName,
Builtin, CreateTarget, ExtCall, FlagMember, For, If, IfExp, IntCall, Pop,
Range, RawCallTarget, RawLog, RawRevert, SelfDestructTarget, Send, StructLit,
Subscript, SubscriptTarget, TopLevelName, TypeBuiltin, exprs_cons, for_cons

## tp_bind_err_tac Instances (21+ in file)
All `TRY (tp_bind_err_tac >> NO_TAC)` need the underlying tactic to work.
Lines: 839, 1012, 1108, 1132, 1185, 1318, 1396, 1420, 1471, 1797, 1805,
2023, 2714, 3723, 3729, 3734
Plus `tp_bind_err_tac >> not_return_tac >> NO_TAC` at: 1930, 1936, 2159, 2283, 2287, 2292
Plus bare `tp_bind_err_tac` at: 864, 1161, 2656, 3742

## CHEAT INVENTORY (6 in helpers file)

| # | Theorem | What it does | Needed by |
|---|---------|-------------|-----------|
| 1 | env_consistent_pop_scope | Pop scope preserves env_consistent | AugAssign, For, IntCall |
| 2 | env_consistent_preserves_tv | Eval preserves tv+env_consistent | Many stmt blocks |
| 3 | bind_arguments_env_consistent | Call arg binding preserves env | IntCall, ExtCall |
| 4 | set_immutable_well_typed | set_immutable preserves typing | Assign, AnnAssign |
| 5 | assign_target_well_typed | Assignment replace preserves typing | Assign, AugAssign, Append |
| 6 | eval_expr_not_HashMapRef | Well-typed eval not HashMapRef | Subscript, Name |

## INR Error Subgoal Anatomy (from interactive HOL)
After `reverse (Cases_on q) >> simp_tac (srw_ss()) []`, the INR subgoal is:
```
INR y = res ∧ st_bt = st' ⇒
  state_well_typed st' ∧ env_consistent env cx st' ∧
  accounts_well_typed st'.accounts ∧
  (∀s. res ≠ INR (Error (TypeError s))) ∧
  ∀v ret_tv. res = INR (ReturnException v) ∧ ... ⇒ value_has_type ...
```
Solution: strip_tac (introduces equalities), then drule_all from IH.
The IH gives: state_well_typed st_bt, env_consistent env cx st_bt,
accounts_well_typed st_bt.accounts, ∀s. INR y ≠ INR (Error (TypeError s)).
With st_bt = st' from strip, most conjuncts follow by gvs[] or ACCEPT_TAC.
Last conjunct follows from eval_*_not_return (INR y never matches INR (ReturnException v)).

## WHAT NOT TO TRY
- `>> TRY (.. >> NO_TAC)` after case splits — silently fails
- `>- (tp_bind_err_tac)` currently — tp_bind_err_tac incomplete for new IH
- `simp[evaluate_def]` without `Once` — HANGS
- `gvs[]` to substitute `expr_type e = BaseT bt` — DOESN'T WORK
- `metis_tac` with many assumptions — TIMES OUT
- `>- (cheat)` when you're not sure which subgoal is targeted — confusing errors

## KEY FILES
- Main theorem: semantics/prop/vyperTypeSoundnessScript.sml (~3998 LOC)
- Helpers: semantics/prop/vyperTypeSoundnessHelpersScript.sml (~7307 LOC, 6 cheats)
- tp_bind_err_tac: line 785 of main theorem file
- not_return_tac: line 185 of main theorem file
- not_type_error_tac: line 248 of main theorem file
- Workdir: semantics/prop/
