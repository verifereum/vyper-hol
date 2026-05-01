# STATE: Type Soundness Repair

## Session 86: Systematic accounts_well_typed propagation

### CRITICAL INSIGHT: accounts_well_typed is a new IH antecedent

The `accounts_well_typed st.accounts` precondition was added to ALL P0-P8 propositions
on this branch. This means **every `drule_all` application of an IH to a derived state
(not the original `st`) needs `accounts_well_typed` established for that derived state first.**

For pushed-scope contexts (`r with scopes updated_by CONS FEMPTY`):
- `state_well_typed` → `irule push_scope_swt`
- `env_consistent` → `irule push_scope_ec`
- `accounts_well_typed` → `simp[evaluation_state_component_equality]` (push_scope doesn't touch accounts)

For `close_inr_err_tac` and error-propagation cases: NO issue, because the state IS
the original `st` or `r`, and `accounts_well_typed` is already in assumptions.

### CHANGES MADE THIS SESSION (untested)

1. **If block** (lines ~1612-1625): Fixed INR case with explicit `>-` and targeted
   `qpat_x_assum ... drule_all` instead of `TRY close_inr_err_tac >> first_x_assum drule_all`.
   INL case uses same `qpat_x_assum` approach.

2. **If_True** (lines ~1657-1663): Added `accounts_well_typed (r with scopes updated_by CONS FEMPTY).accounts`
   establishment via `simp[evaluation_state_component_equality]`. Reverted to `drule_all`
   for IH application (now works because all antecedents are in assumptions).

3. **If_False BoolV F case** (lines ~1683-1688): Same fix — added accounts_well_typed
   establishment, reverted to drule_all.

4. **qpat_assum → qpat_x_assum conversions** (7 of 8): Lines 1239, 1500, 1940, 2009,
   2466, 2857, 3333. Line 1393 (Assign block) MUST stay as `qpat_assum` because it
   creates a new Q.EXISTS-wrapped assumption from the matched one.

5. **NONE of these changes have been tested in a successful build yet.**

### IMMEDIATE PRIORITY — do in this order

**Step 1: Build and check If_True/If_False fix**

The most recent edit added accounts_well_typed for pushed scope state. Build should
now pass at least through If_False. Watch for:
- The `prove(...)` call in If_False error branch (line ~1695)
- Whether `not_type_error_tac` in If_True/If_False still works

**Step 2: Fix For block**

The For block (line ~1702) uses `push_scope_with_var` and likely needs the same
`accounts_well_typed` establishment for the scope-pushed state. Check:

```
`accounts_well_typed (st with scopes updated_by CONS (FEMPTY |+ (nm,<| ... |>))).accounts`
  by simp[evaluation_state_component_equality]
```

**Step 3: Check ALL other blocks for drule_all failures**

Run the build. If it fails at another block with `Q_TAC0/FIRST_ASSAM` or
"predicate not true" error, the fix is likely: establish `accounts_well_typed`
for whatever state the IH is being applied to.

Common patterns where this is needed:
- Blocks using `drule_all` with a state DIFFERENT from `st`
- Specifically: any block that establishes state for a sub-computation
  (push_scope, with_var, etc.)

**Step 4: Fix remaining cheated blocks**

### CHEATED HELPERS (6 in vyperTypeSoundnessHelpersScript.sml)

1. env_consistent_pop_scope (line ~1380)
2. env_consistent_preserves_tv IntCall (line ~1536)
3. env_consistent_preserves_tv ExtCall (line ~1593)
4. assign_target_no_type_error (line ~1913)
5. set_immutable_well_typed (line ~2028)
6. eval_expr_not_HashMapRef Call case (line ~7276)

### CHEATED MAIN BLOCKS (3 in vyperTypeSoundnessScript.sml)

1. Assert3 (line ~1326)
2. Append (line ~1334)
3. AugAssign_atwt (line ~1577)

### qpat_assum STATUS

Line 1393 (Assign block) MUST stay as `qpat_assum` — it wraps the matched assumption
with Q.EXISTS to create a new existential, and the original is needed.

### BUILD INFORMATION

- `holmake(workdir="semantics/prop", timeout=1200)`
- Full build ~730s from scratch; incremental ~80-120s to failure point
- Error pattern: FIRST_ASSAM/Q_TAC0 → missing assumption for drule_all
- Error pattern: "predicate not true" → prove() call or assert in tactic fails
- Error pattern: "unsolved goals: F" → simp oversimplified using wrong IHs

### KEY ARCHITECTURAL INSIGHTS

1. Guarded IHs only in If/IfExp/For (from push_scope composition).
   close_inr_err_tac works for all other blocks.
2. accounts_well_typed must be established for derived states before drule_all.
3. push_scope doesn't change accounts → simp[evaluation_state_component_equality].
4. `qspecl_then + simp[]` is DANGEROUS when multiple similar IHs are in assumptions
   (simp may instantiate variables incorrectly, producing F).
5. `drule_all` is the RIGHT approach when ALL IH antecedents are in assumptions.
   The fix is establishing missing assumptions, not changing the tactic.
