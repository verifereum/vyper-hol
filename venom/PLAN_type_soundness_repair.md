# PLAN: Type Soundness Proof Repair

## Goal

Make `semantics/prop/` build with:

```text
Holmake --qof
0 FAIL
0 CHEAT warnings
```

Target theorem path:

```text
semantics/prop/vyperTypeSoundnessScript.sml
  eval_preserves_swt
  type_preservation
```

The theorem statements are frozen by `venom/TASK_type_soundness_repair.md`; do not weaken them. If a statement is false, produce a concrete HOL4 counterexample and the tightest fix.

## Current failure frontier

Build currently reaches `eval_preserves_swt[For]` after recent `If_False` repair. Work proceeds strictly by the first Holmake failure; do not skip ahead except to extract helper lemmas needed by that failure.

Immediate checkpoints:

```text
1. Stabilize If_False/For so Holmake advances past For.
2. Continue Holmake failure-driven repair through remaining Resume blocks.
3. Discharge all cheats in type-soundness helper/main files.
4. Rebuild semantics/prop with zero CHEAT warnings.
```

## Proof strategy

### 1. Preserve theorem structure

Use the existing `suspend`/`Resume` architecture. For each failing block:

```text
hol_state_at at failing tactic
inspect exact goal
edit smallest local proof step
holmake semantics/prop to expose next failure
```

Avoid global tactic rewrites unless a repeated pattern is proven safe.

### 2. Accounts invariant pattern

`accounts_well_typed st.accounts` is now an antecedent of every mutual IH. Before applying an IH to a derived state, explicitly establish it.

Common derived-scope state:

```sml
`accounts_well_typed (r with scopes updated_by CONS FEMPTY).accounts` by
  simp[evaluation_state_component_equality]
```

For state-changing operations, use/derive operation boundary lemmas instead of assuming accounts are unchanged.

### 3. Guarded IH pattern

Guarded IHs occur mainly around `If`, `IfExp`, and `For` compositions. Do not use blind `first_x_assum drule_all`; select the intended IH by shape.

Examples:

```sml
qpat_x_assum `!env typ st res st'. well_typed_iterator _ _ it /\ _ ==> _`
  drule_all >> strip_tac
```

For generated higher-order guards, specialize the guard explicitly, then apply the resulting IH.

### 4. No-TypeError pattern

For propagated errors, prove contradiction or forward IH no-TypeError; do not try to prove a false no-TypeError conclusion after simplifying to `res = INR (Error (TypeError _))` unless assumptions contradict that branch.

Useful boundaries:

```text
materialise_well_typed_no_type_error
assign_target_no_type_error       (currently cheated; must prove)
pure_op_not_return / evaluate_no_return conjuncts
```

### 5. Helper-cheat discharge order

Discharge helper cheats before relying on main theorem closure:

```text
A. assign_target_no_type_error
   Needed by Assign/AugAssign no-TypeError branches.

B. env_consistent_pop_scope
   Needed by for/scope cleanup and env restoration.

C. env_consistent_preserves_tv variants
   Needed by call/state-preservation chains.

D. bind_arguments_env_consistent
   Needed by IntCall body setup.

E. set_immutable_well_typed
   Needed by immutable assignment target preservation.

F. eval_expr_not_HashMapRef Call case
   Needed by materialise no-TypeError bridge.
```

Main proof cheats to discharge after dependent helpers:

```text
Assert3
Append
AugAssign_atwt
```

## Validation loop

Use MCP HOL tools only for HOL interaction:

```text
hol_state_at(file, line, col)
hol_check_proof(file, theorem)
holmake(workdir="semantics/prop")
```

Completion requires:

```text
git grep -n "cheat" -- semantics/prop/vyperTypeSoundness*.sml
# no proof cheats in target files

holmake(workdir="semantics/prop", timeout=120)
# succeeds; no CHEAT warnings
```

## Constraints

- Do not edit interpreter semantics to make proofs easier.
- Do not weaken `eval_preserves_swt` or `type_preservation`.
- No new duplicate near-helper lemmas; generalize once and reuse.
- No network operations; only local `main` merge if requested by task flow.
