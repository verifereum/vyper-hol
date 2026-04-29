# STATE: Type Soundness Repair

## IMMEDIATE NEXT ACTION

### Step 1: Fix Assert3 — remove `by` block, inline derivation after RULE_ASSUM_TAC
Current code (lines 1109-1121) has a `by` block that fails because after RULE_ASSUM_TAC
rewrites `expr_type e → BaseT BoolT` in assumptions, the `by` block's internal tactics
(`imp_res_tac >> Cases_on >> gvs >> irule >> simp`) still fail for unknown reasons.

**Fix**: Remove the `by` block entirely. Inline:
```sml
  (* INL case: apply IH for e *)
  first_x_assum drule_all >> strip_tac >>
  first_x_assum (qspec_then `x` assume_tac) >>
  (* Rewrite expr_type e in all assumptions so imp_res_tac can match *)
  qpat_x_assum `expr_type e = BaseT BoolT` (fn th =>
    RULE_ASSUM_TAC (ONCE_REWRITE_RULE[th])) >>
  (* x must be Value vl: BaseT type means tyv ≠ NoneTV and tyv ≠ ArrayTV *)
  imp_res_tac toplevel_value_typed_for_BaseT >>
  Cases_on `x` >> gvs[toplevel_value_typed_def] >>
  first_x_assum irule >> simp[] >>
```

**KEY DEBUG STEP**: Before building, use `hol_state_at` interactively to inspect
the goal state after RULE_ASSUM_TAC. Verify assumptions contain
`evaluate_type (get_tenv cx) (BaseT BoolT) = SOME tyv` literally.

If `toplevel_value_typed_for_BaseT` with `imp_res_tac` doesn't work (adds ∃ as
assumption instead of solving goal), try instead:
```sml
  drule toplevel_value_typed_for_BaseT >> strip_tac >> gvs[]
```
Or use `toplevel_value_typed_for_BaseT_expr_type` with `irule`:
```sml
  irule toplevel_value_typed_for_BaseT_expr_type >> rpt (first_assum ACCEPT_TAC)
```

### Step 2: Fix second `by` block in Assert3 (line ~1145)
After the switch_BoolV case, the e' evaluation produces same pattern:
`?sv. x' = Value sv` by (`imp_res_tac evaluate_type_BaseT_inv >> Cases_on >> gvs >> irule >> simp[]`)
This may need the same RULE_ASSUM_TAC fix for `expr_type e' = BaseT (StringT n)`.

### Step 3: Prove Category A blocks (Name, BareGlobalName, TopLevelName, etc.)
All expression evaluation blocks will need the same RULE_ASSUM_TAC pattern.
Consider extracting a reusable tactic:
```sml
val rewrite_expr_types_tac =
  TRY (qpat_x_assum `expr_type e = BaseT bt` (fn th =>
    RULE_ASSUM_TAC (ONCE_REWRITE_RULE[th]))) >>
  TRY (qpat_x_assum `expr_type e' = BaseT bt` (fn th =>
    RULE_ASSUM_TAC (ONCE_REWRITE_RULE[th])))
```

## BLOCK STATUS

### PROVED (22 blocks):
Assert1, Assert2, AttributeTarget, BareGlobalNameTarget, BaseTarget, Break, Continue, Expr,
Log, NameTarget, Pass, Raise1, Raise2, Raise3, ReturnNone, ReturnSome,
TopLevelNameTarget, TupleTarget, stmts_cons, stmts_nil, targets_cons, targets_nil

### IN PROGRESS (1 block):
Assert3 — `by` block decomposition wrong, need to inline derivation

### UNATTEMPTED (33 blocks):
Category A (LOW): Name, BareGlobalName, TopLevelName, FlagMember, Literal,
  IfExp, StructLit, Subscript, Attribute, Builtin, Pop, TypeBuiltin
Category B (MEDIUM): If, AugAssign, AnnAssign, Assign, Append, Array, Range
Category C (MEDIUM): For, for_cons, for_nil
Category D (HIGH): ExtCall, IntCall, Send, RawCallTarget, RawLog, RawRevert,
  SelfDestructTarget, CreateTarget
Category E (LOW): exprs_cons, exprs_nil

## KEY DISCOVERY THIS SESSION

### RULE_ASSUM_TAC works for expr_type substitution
`qpat_x_assum `expr_type e = BaseT BoolT` (fn th => RULE_ASSUM_TAC (ONCE_REWRITE_RULE[th]))`
successfully rewrites `expr_type e → BaseT BoolT` across ALL assumptions without
causing timeout. This is THE fix for the `imp_res_tac` silent matching failure.

### BUT: `by` blocks still fail after RULE_ASSUM_TAC
Even with correct assumptions, the `by` block containing
`imp_res_tac >> Cases_on >> gvs >> irule >> simp` fails at line 1117.
Root cause unknown — need interactive `hol_state_at` to inspect post-RULE_ASSUM_TAC goal.

### `by` block is the wrong decomposition
The `by` block creates a sealed subproof. For Assert3's rich context, this causes
silent failures. Fix: inline the derivation without `by`.

## NEW LEMMA (compiled, proved)
`toplevel_value_typed_for_BaseT_expr_type` in helpers file at line ~4243:
  `!tenv e bt tv tyv.
    evaluate_type tenv (expr_type e) = SOME tyv /\
    expr_type e = BaseT bt /\
    toplevel_value_typed tv tyv ==>
    ?v. tv = Value v`
Takes the EXACT assumption shape from IH output. May not need RULE_ASSUM_TAC at all
if used with `irule` in main flow.

## CHEAT INVENTORY (6 in vyperTypeSoundnessHelpersScript.sml)

| # | Theorem | Line | What it does | Needed by |
|---|---------|------|-------------|-----------|
| 1 | env_consistent_pop_scope | ~1347 | Pop scope preserves env_consistent | AugAssign?, For?, IntCall? |
| 2 | env_consistent_preserves_tv | ~1503 | Evaluation preserves tv+env_consistent | Multiple stmt blocks |
| 3 | bind_arguments_env_consistent | ~1560 | Call argument binding preserves env | IntCall?, ExtCall? |
| 4 | set_immutable_well_typed | ~1982 | set_immutable preserves typing | Assign?, AnnAssign? |
| 5 | assign_target_well_typed | ~2364 | Assignment preserves typing (set_immutable case) | Assign, AugAssign |
| 6 | eval_expr_not_HashMapRef | ~7189 | well_typed NoneT eval never HashMapRef | Subscript?, Name? |

## WHAT NOT TO TRY
- `by` blocks with `imp_res_tac` chains in rich proof contexts (silently fails)
- `gvs[]` in Assert3 context (causes timeout, likely due to guarded IH for e')
- Nested ML `qpat_x_assum` with `fn th1 => qpat_x_assum ... (fn th2 => ...)` (causes timeout)
- `metis_tac` with many assumptions in Assert3 context (diverges)
- `fs[]` to cross-rewrite `expr_type e` in assumptions (doesn't work reliably)

## REUSABLE TACTIC PATTERN
For ALL expression evaluation Resume blocks, after IH application produces
`evaluate_type (get_tenv cx) (expr_type e) = SOME tyv` + `expr_type e = BaseT bt`:
1. `qpat_x_assum `expr_type e = BaseT bt` (fn th => RULE_ASSUM_TAC (ONCE_REWRITE_RULE[th]))`
2. Then `imp_res_tac toplevel_value_typed_for_BaseT` matches
3. Derive `?v. x = Value v` inline (not in `by` block)

## KEY FILES
- Main theorem: semantics/prop/vyperTypeSoundnessScript.sml (~4048 lines)
- Helpers: semantics/prop/vyperTypeSoundnessHelpersScript.sml (~7305 lines)
- Definitions: semantics/prop/vyperTypeSoundnessDefsScript.sml
- Builtin typing: semantics/prop/vyperBuiltinTypingScript.sml
- Workdir: semantics/prop/

## ORACLE FEEDBACK
No oracle calls this session. All attempts were manual tactic search.
For Assert3, an oracle call is NOT needed — the fix is known (inline derivation),
just needs interactive verification.
