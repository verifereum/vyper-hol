# STATE: Type Soundness Repair

## Session 18: ZERO theorems proved. Root cause of Append failure identified.

## ROOT CAUSE (high confidence, needs HOL verification)

**`first_x_assum drule_all` at line 1176 consumes the WRONG IH.** 

In the Append proof, after `eval_base_target cx bt st = (INL (loc, sbs), st_bt)` is
established, there are TWO ∀-assumptions:
1. **P5 IH**: `∀env st res st'. (∃ty. well_typed_target env bt ty) ∧ ... ⇒ ...`
2. **Guarded P7 IH**: `∀s'' loc sbs t'. eval_base_target cx bt s'' = (INL (loc,sbs),t') ⇒ ∀env st ...`

`first_x_assum drule_all` picks the NEWEST (∴ guarded P7), matches its antecedent
`eval_base_target cx bt s'' = (INL (loc,sbs),t')` against the assumption, and
consumes it. The guarded P7 IH is then GONE.

When lines 1188-1193 try to find the guarded P7 IH again, it doesn't exist → FIRST_ASSAM error.

**Evidence:** `first_x_assum (fn th => if ... same_const u ``eval_base_target`` ... then ...)`
at line 1188 also fails with FIRST_ASSAM — confirming no ∀-assumption containing
`eval_base_target` remains.

## FIX PLAN (next session MUST do this first)

### Step 1: Verify (30 seconds)
```sml
hol_state_at(line=1177, file="semantics/prop/vyperTypeSoundnessScript.sml")
```
After `first_x_assum drule_all >> strip_tac`, check if guarded P7 IH is still in assumptions.

### Step 2: Fix line 1176 — targeted P5 selection
Replace `first_x_assum drule_all >> strip_tac` with something that ONLY matches P5.
Option A (if qpat_x_assum parses it):
```sml
qpat_x_assum `∀env st res st'. (∃ty. well_typed_target _ _ ty) ∧ _ ⇒ _` drule_all >> strip_tac
```
Option B (robust, uses let-bound predicate defined BEFORE the proof):
```sml
(* Define outside proof: *)
val is_well_typed_target_ih = fn th => is_forall (concl th) andalso
  can (find_term (fn u => same_const u ``well_typed_target``)) (concl th) andalso
  not (can (find_term (fn u => same_const u ``eval_base_target``)) (concl th));
(* Then in proof: *)
first_x_assum (fn th => if is_well_typed_target_ih th then drule_all th else NO_TAC) >> strip_tac
```

### Step 3: Fix lines 1188-1193 — guarded P7 IH application
After Step 2, the guarded P7 IH should still be in scope. Replace:
```sml
qpat_x_assum `!s'' loc' sbs' t'. eval_base_target _ _ _ = _ ==> _`
  (qspecl_then [`st`, `loc`, `sbs`, `st_bt`] mp_tac) >>
(impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
qpat_x_assum `!env' st0 res0 st0'. well_typed_expr _ _ /\ _ ==> _`
  (qspecl_then [`env`, `st_bt`, `INL x`, `r`] mp_tac) >>
(impl_tac >- (rpt CONJ_TAC >> first_assum ACCEPT_TAC)) >> strip_tac >>
```
With (using same let-bound predicate approach):
```sml
first_x_assum (fn th => if is_forall (concl th) andalso
  can (find_term (fn u => same_const u ``eval_base_target``)) (concl th)
  then drule_all th else NO_TAC) >> strip_tac >>
qpat_x_assum `∀env st res st'. well_typed_expr _ _ ∧ _ ⇒ _` drule_all >> strip_tac >>
```
NOTE: The `same_const` inside `fn th => ...` may not work inside proof context
(Session 18 finding). If so, define the predicate OUTSIDE the proof as a val binding.

### Step 4: Define `apply_guarded_ih` tactic (generalize)
After validating on Append, extract a general tactic:
```sml
(* Apply a guarded IH by finding it via head constant, then drule_all *)
fun apply_guarded_ih head_const =
  first_x_assum (fn th => if is_forall (concl th) andalso
    can (find_term (fn u => same_const u head_const)) (concl th)
    then drule_all th else NO_TAC) >> strip_tac
```

### Step 5: Apply fix to ALL 14 `impl_tac >- ACCEPT_TAC` occurrences

### Step 6: Also fix ALL ~30 `first_x_assum drule_all` in untested blocks
Some of these may also have the same wrong-IH problem. Use targeted selection.

### Step 7: Full failure inventory
After fixing Append, cheat remaining untested blocks, build, count cheats.

## BLOCK STATUS (82 total)

### VERIFIED WORKING in holmake (27):
Pass, Continue, Break, ReturnNone, ReturnSome, Raise1, Raise2, Raise3, Assert1,
Assert2, Log, Expr, stmts_nil, stmts_cons, BaseTarget, TupleTarget,
targets_nil, targets_cons, NameTarget, BareGlobalNameTarget,
TopLevelNameTarget, AttributeTarget, for_nil, Name, Literal, exprs_nil

### CHEATED — needs proof (1):
Assert3 (cheated in session 16)

### UNTESTED — build fails at Append before reaching these (~54):
AnnAssign, Append_atwt, Assign, Assign_atwt, AugAssign, AugAssign_atwt,
If, If_True, If_False, For, Array, Range, SubscriptTarget, for_cons,
BareGlobalName, TopLevelName, FlagMember, IfExp, IfExp_True, IfExp_False,
StructLit, Subscript, Subscript_tail, Subscript_result, Subscript_INL,
Subscript_INR, Attribute, Builtin, Builtin_Len, Builtin_Len_main,
Builtin_NonLen, Builtin_INL, Pop, Pop_vht, TypeBuiltin, Send, ExtCall,
IntCall, intcall_tail, dflts_ih, intcall_chain, intcall_inl,
chain_sc, chain_bind, chain_bind_swt, chain_bind_ec, chain_ih,
chain_every_swt, RawCallTarget, RawLog, RawRevert,
SelfDestructTarget, CreateTarget, exprs_cons

### CHEATS in helpers file (6):
| Line | Theorem | What |
|------|---------|------|
| 1347 | env_consistent_pop_scope | Pop scope preserves env_consistent |
| 1503 | env_consistent_preserves_tv | Eval preserves tv+env_consistent |
| 1560 | bind_arguments_env_consistent | Call arg binding preserves env |
| 1982 | set_immutable_well_typed | set_immutable preserves typing |
| 2364 | assign_target_well_typed | Assignment replace preserves typing |
| 7206 | eval_expr_not_HashMapRef | Well-typed eval not HashMapRef |

## PRIORITY ORDER (next session)

1. **Verify root cause** at line 1176 via hol_state_at (1 min)
2. **Fix line 1176** — targeted P5 selection (5 min)
3. **Fix lines 1188-1193** — guarded P7 drule_all (5 min)
4. **Validate Append** via holmake (2 min)
5. **Define apply_guarded_ih** and replace all 14 impl_tac>ACCEPT_TAC (30 min)
6. **Fix Assert3** — use switch_BoolV_cases boundary lemma (15 min)
7. **Full inventory** — cheat remaining untested blocks, build, count (10 min)
8. **Systematic repair** — fix blocks by category

## WHAT NOT TO TRY
- `qpat_x_assum` with primed variables (`s''`, `loc'`) → Q_TAC0 error
- `first_x_assum drule_all` when multiple ∀-IHs exist → consumes wrong IH
- `same_const u ``const_name``` inside fn th => ... within proof quotations
- `Cases_on v` where `v : value` → TIMEOUT
- `>- (* INR case *)` after `Cases_on q` → targets wrong subgoal
- `qspecl_then` with backtick terms → TYPE ERRORS
- `simp[AllCaseEqs()]` on monadic bind chains → TIMEOUT

## KEY FILES
- Main theorem: semantics/prop/vyperTypeSoundnessScript.sml (~3985 LOC)
- Helpers: semantics/prop/vyperTypeSoundnessHelpersScript.sml (~7307 LOC)
- Workdir: semantics/prop/

## ORACLE FEEDBACK
Session 18 oracle (anthropic/claude-opus-4.6): Identified `drule_all` as replacement
for `qspecl_then + impl_tac`, which was directionally correct. But missed that
`first_x_assum drule_all` at line 1176 was the actual root cause — oracle focused
on the explicit failure point rather than the earlier silent IH consumption.
When using oracle for debugging, always ask it to examine ALL `first_x_assum`
calls in the preceding proof steps, not just the failing line.
