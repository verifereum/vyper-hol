# Fix proof theories after default parameter values change

## Background

Commit `0dc3a9b` ("implement default parameter values") changed the IntCall
semantics. The `eval_expr` definition for `Call (IntCall ...)` now evaluates
default argument expressions before entering the function body:

```
vs       <- eval_exprs cx es;                    (* explicit args *)
needed_dflts <<- DROP (...) dflts;
cxd      <<- cx with stk updated_by CONS (src_id_opt, fn);
dflt_vs  <- eval_exprs cxd needed_dflts;         (* NEW: default args *)
env      <- lift_option (bind_arguments ...);
prev     <- get_scopes;                           (* save scopes *)
...
rv       <- finally (try body handle_function) (pop_function prev);
```

This has two consequences for scope-related proofs:

1. **scope_preserving_expr for Call is unsound.** The defaults are arbitrary
   expressions from the function definition. They are evaluated BEFORE
   `get_scopes` captures `prev`, so if they modify scopes, the `finally`
   block restores the wrong value. The `scope_preserving_expr` predicate
   checked only the explicit args and `drv`, not the defaults. Fix: set
   `scope_preserving_expr (Call _ _ _) = F`. This has been done.

2. **Structural induction on `expr` is insufficient for scope-domain
   preservation.** The defaults come from a runtime function lookup, not
   from the Call syntax tree. The structural IH covers only `es` and `drv`.
   There is no IH for `eval_exprs cxd needed_dflts`.

---

## Part 1: vyperScopePreservingExprScript.sml

### Status
Build fails at `case_IntCall` (line 375).

### Problem
The `case_IntCall` theorem statement has the old IH shape
(`check (LENGTH args = LENGTH es)`), and the proof cannot handle the new
`eval_exprs cxd needed_dflts` step.

### Fix (straightforward)
With `scope_preserving_expr (Call _ _ _) = F`, all Call cases become
vacuously true. The conclusion of each Call case lemma has
`scope_preserving_expr (Call ...) ==> ...`, which reduces to `F ==> ...`.

**Changes:**

1. Delete `case_Send`, `case_ExtCall`, `case_IntCall` (lines 207-404).
   Replace with a single lemma or handle inline:
   ```
   Theorem case_Call[local]:
     !cx c es drv st res st'.
       eval_expr cx (Call c es drv) st = (res, st') ==>
       scope_preserving_expr (Call c es drv) ==> st.scopes = st'.scopes
   Proof
     rw[scope_preserving_expr_def]
   QED
   ```
   This works because the catch-all `_ = F` covers all Call forms.

2. In `expr_scopes_mutual` (line 472), the Call subgoals from
   `evaluate_ind` all have `scope_preserving_expr (Call ...) ==> ...` in the
   conclusion. Close them with `simp[scope_preserving_expr_def]` instead of
   `ACCEPT_TAC case_Send'` etc.

3. The `expr_scopes_ind_principle` specialization (line 452) should still
   work — it has the same 9 predicates. But the assembly in
   `expr_scopes_mutual` needs updating because:
   - The number of `evaluate_ind` subgoals may have changed (ExtCall now
     has a new `drv` recursive call, IntCall has the defaults call).
   - The old `ACCEPT_TAC case_IntCall'` pointed at a theorem whose
     statement no longer matches.

   Since all Call subgoals are now trivial, the simplest fix is to use
   a blanket `TRY (simp[scope_preserving_expr_def])` after handling the
   non-Call cases. This avoids needing to count or match subgoal order.

### Net effect
~200 lines of complex Call proofs are replaced by ~5 lines.

---

## Part 2: vyperEvalExprPreservesScopesDomScript.sml

### Status
Does not build (depends on Part 1). Even after Part 1 is fixed,
`case_Call_IntCall_ind` will fail.

### Problem
This file proves the unconditional property (no `scope_preserving_expr`
precondition):

```
!e cx st res st'.
  eval_expr cx e st = (res, st') ==>
  MAP FDOM st.scopes = MAP FDOM st'.scopes
```

It uses **structural induction** on the `expr` type. The structural IH for
`Call (IntCall ...) es drv` provides only:

```
!e. MEM e es ==> P(e)     (* explicit args are subterms *)
drv = SOME e ==> P(e)     (* drv is a subterm *)
```

The default expressions `needed_dflts` come from `lookup_callable_function`
at runtime. They are not syntactic subterms of the Call, so the structural
IH says nothing about them.

The proof needs to show that `eval_exprs cxd needed_dflts` preserves scope
domains, but has no way to establish this.

### Fix: switch from structural induction to `evaluate_ind`

The `evaluate_ind` principle is generated from the mutually recursive
`evaluate_def`. It provides IHs for ALL recursive calls, including the
defaults. Inspecting it in a HOL session shows:

- **45 total subgoals**, 9 predicates (P0-P8)
- P0 (eval_stmt, 15 cases), P1 (eval_stmts, 2), P2 (eval_iterator, 2),
  P3 (eval_target, 2), P4 (eval_targets, 2), P6 (eval_for, 2)
  — all set to T, closed with `simp[]`
- P5 (eval_base_target, 4 cases), P7 (eval_expr, 14 cases),
  P8 (eval_exprs, 2 cases) — need real proofs

The IntCall subgoal from `evaluate_ind` provides 3 IH conjuncts:

- **IH for `eval_stmts cxf body`** (P1 = T): trivially true.
- **IH for `eval_exprs cxd needed_dflts`** (P8, guarded by checks +
  eval_exprs cx es succeeding): gives domain preservation for defaults.
- **IH for `eval_exprs cx es`** (P8, guarded by checks succeeding):
  gives domain preservation for explicit args.

The IH for defaults is the missing piece that structural induction could
not provide.

### Proof sketch for IntCall with `evaluate_ind`

**Theorem:** If `eval_expr cx (Call (IntCall (src_id_opt, fn)) es drv) st = (res, st')`,
then `MAP FDOM st'.scopes = MAP FDOM st.scopes`.

**Proof by cases on where evaluation terminates:**

- *Before eval_exprs cx es (checks/lookups fail):* All operations are pure
  (check, lift_option on pure functions). State is unchanged, so
  `st' = st` modulo non-scope fields. Scopes trivially preserved.

- *eval_exprs cx es fails:* The do-block short-circuits. The IH for
  `eval_exprs cx es` (IH3) says this call preserves scope domains.
  Its guard (checks succeeded) is satisfied because we reached this point.
  So `MAP FDOM st'.scopes = MAP FDOM st.scopes`.

- *eval_exprs cx es succeeds, eval_exprs cxd needed_dflts fails:*
  The do-block short-circuits. IH3 gives domain preservation through
  the explicit args evaluation. IH2's guard is satisfied (checks succeeded
  AND eval_exprs cx es succeeded). IH2 gives domain preservation through
  the defaults evaluation. Chaining: `MAP FDOM st'.scopes = MAP FDOM
  (state after es).scopes = MAP FDOM st.scopes`.

- *Both eval_exprs calls succeed, but something later fails before finally
  (bind_arguments, evaluate_type):* These are pure operations
  (lift_option on pure functions). State unchanged from after defaults
  evaluation. Domain preserved by IH2 + IH3 chain.

- *Execution reaches finally:* `get_scopes` captures `prev` = scopes
  after defaults. `finally ... (pop_function prev)` always runs
  `set_scopes prev`, so `st'.scopes = prev`. By `finally_set_scopes_dom`,
  `MAP FDOM st'.scopes = MAP FDOM prev`. By IH2 + IH3 chain,
  `MAP FDOM prev = MAP FDOM st.scopes`. QED.

### Detailed change plan

#### Step 1: Create specialized `evaluate_ind` (~15 lines)

Specialize `evaluate_ind` with:
- P0-P4, P6 = `\cx args. T`
- P5 = domain preservation for eval_base_target
- P7 = domain preservation for eval_expr
- P8 = domain preservation for eval_exprs

Use `SPECL` + `DEPTH_CONV BETA_CONV`, same technique as in
`vyperScopePreservingExprScript.sml` (line 452).

#### Step 2: Delete structural induction infrastructure

Remove the local definitions `scopes_P0_def` through `scopes_P5_def`
(lines 311-333) and the structural induction proof using
`ho_match_mp_tac (TypeBase.induction_of ":expr")` (line 343).

#### Step 3: Adapt helper lemmas

For each `evaluate_ind` subgoal, either reuse, adapt, or inline.

**No change needed (6 cases):**
- `case_NameTarget_dom`, `case_TopLevelNameTarget_dom`: no IH, standalone.
- Name, TopLevelName, FlagMember, Literal: no IH. These were proven
  inline in the structural induction; the same tactics work.

**Nearly identical IH shape (3 cases):**
- Attribute: `evaluate_ind` gives `P7 cx e ==> P7 cx (Attribute e id)`.
  Current `case_Attribute_ind` has the same shape (unguarded IH).
  Only difference: `cx` is not universally quantified inside the IH.
  Proof: apply IH to the eval_expr sub-call, then chain with
  get_Value/lift_sum/return scopes lemmas. Essentially unchanged.

- Pop: `evaluate_ind` gives `P5 cx bt ==> P7 cx (Pop bt)`.
  Current `case_Pop_ind` has the same shape. Proof unchanged.

- AttributeTarget: `P5 cx t ==> P5 cx (AttributeTarget t id)`.
  Unguarded IH. Current proof works.

**IH becomes simpler — direct P8 instead of per-element (5 cases):**
- StructLit: `evaluate_ind` gives
  `(ks = MAP FST kes ==> P8 cx (MAP SND kes)) ==> P7 cx (StructLit ...)`.
  The IH gives eval_exprs preservation directly. No need for
  `eval_exprs_preserves_scopes_dom_helper`. Proof: unfold definition,
  apply P8 IH to the eval_exprs call. Simpler than before.

- Builtin, TypeBuiltin, Send: `evaluate_ind` gives
  `(check ... ==> P8 cx es) ==> P7 cx (Builtin/TypeBuiltin/Call Send ...)`.
  The guard is just the length check succeeding. In the proof, after
  unfolding the definition, we are in the branch where the check
  succeeded, so the guard is satisfied. Apply P8 to eval_exprs. Simpler
  than before.

- ExtCall: `evaluate_ind` gives `P8 cx es` (unguarded for explicit args)
  plus a heavily-guarded `P7 cx (THE drv)` for the default return value
  path. Current `case_Call_ExtCall_ind` already handles drv; adapt the
  IH shape. Proof: apply P8 for args, for the drv path discharge the
  guard from assumptions and apply P7.

**Guarded IH adaptation needed (4 cases):**
- IfExp: `evaluate_ind` gives `P7 cx e` (unguarded) for the condition,
  and guarded `P7 cx e0`, `P7 cx e1` (guard: `eval_expr cx e s'' =
  (INL tv, t)`). Proof: first show domain preservation for the condition
  via unguarded IH. Then we are in the branch where the condition
  succeeded, providing the guard witness. Apply guarded IH for the
  chosen branch.

- Subscript: `P7 cx e1` unguarded, `P7 cx e2` guarded by e1 succeeding.
  Same pattern: prove e1 preserves domain, use the success witness to
  discharge e2's guard.

- SubscriptTarget: `P5 cx t` unguarded, `P7 cx e` guarded by
  `eval_base_target cx t s'' = (INL (loc,sbs), t')`. Same pattern.

- eval_exprs cons: `P7 cx e` unguarded, `P8 cx es` guarded by
  `eval_expr cx e s'' = (INL tv, t)` and `get_Value tv s''' = (INL v, t')`.
  Prove domain preservation for e, use success witness for the guard,
  apply P8 for the tail.

**Major rewrite (1 case):**
- IntCall: see proof sketch above.

#### Step 4: Rewrite main theorem

Replace the structural induction proof of `eval_mutual_preserves_scopes_dom`
with:

```
MP_TAC scopes_dom_ind >> impl_tac >- (
  rpt conj_tac >>
  TRY (simp[]) >>    (* closes 25 trivially-T statement subgoals *)
  (* then handle P5/P7/P8 cases, either via ACCEPT_TAC of helpers
     or inline tactics *)
) >> simp[]
```

#### Step 5: Keep exported theorems unchanged

`eval_expr_preserves_scopes_dom`, `eval_exprs_preserves_scopes_dom`,
`eval_base_target_preserves_scopes_dom`, and all corollaries
(`preserves_var_in_scope`, `preserves_scopes_len`) are extracted from
the mutual theorem. Their statements and proofs (`metis_tac[...]`) are
unchanged.

#### Step 6: Simplify `eval_exprs_preserves_scopes_dom_helper`

This helper converts per-element IH to eval_exprs preservation. With
`evaluate_ind`, the main proof gets P8 directly and doesn't need this
conversion. The helper can be removed from the main proof, but keep it
if downstream theories use `eval_exprs_preserves_scopes_dom` (which
depends on it at line 455).

### Estimated effort

- Part 1 (ScopePreservingExpr): Small. ~200 lines deleted, ~20 added.
- Part 2 (ScopesDom): Moderate. Most helper adaptations are mechanical.
  IntCall is the only case requiring real new proof content, and it follows
  a clear pattern (chain IH2 + IH3 + finally_set_scopes_dom).
  ~200-300 lines changed, net size roughly similar.

---

## Part 3: vyperEvalPreservesImmutablesDomScript.sml

### Status
Build fails due to `Call` constructor change (2 args → 3 args) and
`lookup_callable_function` tuple change (4-tuple → 5-tuple).

### Problem
Separate from the scope issues above. This file already uses `evaluate_ind`
(not structural induction), so the default-args IH is available. The fixes
are pattern updates and IH shape matching.

### Changes needed

1. **Pattern fixes:** Add `_` or `drv` to all `Call` patterns:
   - `Call Send es` → `Call Send es _`
   - `Call (ExtCall ...) es` → `Call (ExtCall ...) es drv`
   - `Call (IntCall ...) es` → `Call (IntCall ...) es _`

2. **case_Send_imm_dom:** Update IH to match new `evaluate_ind` shape.

3. **case_ExtCall_imm_dom:** Add IH and proof for the new `drv` recursive
   call path (`returnData = []` and `IS_SOME drv`).

4. **case_IntCall_imm_dom:**
   - Update tuple destructuring for the 5-tuple.
   - Update check from `LENGTH args = LENGTH es` to
     `LENGTH es <= LENGTH args /\ ...`.
   - Add IH for `eval_exprs cxd needed_dflts` (available from
     `evaluate_ind`).
   - For immutables-dom, the proof structure is similar to the old one:
     `finally` restores scopes, and immutables are a separate field.
     The new `eval_exprs` call for defaults should preserve immutables-dom
     by the new IH.

5. **Main induction (immutables_dom_mutual):** May need additional `>-`
   entries for new `evaluate_ind` subgoals generated by the `drv` and
   defaults recursive calls.

### Estimated effort
Moderate. Pattern fixes are mechanical. IH updates require interactive
proof development to match the exact shapes.
