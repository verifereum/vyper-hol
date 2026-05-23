# STATE_type_system_rewrite
Updated: 2026-05-23

## Cursor
- component: C2.4.1.1
- status: ready
- active_file: semantics/vyperStateScript.sml
- next_action: Continue active component C2.4.1.1 only. Edit `toplevel_array_length_def` to add a case before the catch-all: `toplevel_array_length cx (Value (ArrayV (SArrayV sparse))) = return $ &(LENGTH sparse)`. Then add a small positive regression theorem (prefer near the definition or in the earliest suitable proof file per PLAN) with shape `toplevel_array_length cx (Value (ArrayV (SArrayV sparse))) st = (INL (&LENGTH sparse), st)`. Do not yet work on C2.4.1.2 cleanup or the Expr_Builtin resume.
- expected_goal_shape: After editing the definition, the old local TypeError probe in `vyperTypeStmtSoundnessScript.sml` may fail because the bug is fixed. For C2.4.1.1, first verification should show either the direct SArrayV length regression proves by `simp[toplevel_array_length_def, return_def]`, or build stops at stale counterexample probes slated for C2.4.1.2 cleanup. The intended computation is `(INL (&LENGTH sparse), st)`, not `INR (Error (TypeError ...))`.
- verify_with: holbuild(targets=["vyperTypeStmtSoundnessTheory"], timeout=600) for current downstream visibility; if definition-only regression is placed in `vyperStateScript.sml`, `holbuild(targets=["vyperStateTheory"], timeout=600)` is a faster first check.

## If This Fails
- If the SArrayV regression itself fails, inspect generated/failed goal and fix the new `toplevel_array_length_def` equation. If the build instead fails at old local counterexample theorems in `vyperTypeStmtSoundnessScript.sml`, checkpoint C2.4.1.1 progress with evidence if the definition/regression is accepted, then proceed only to C2.4.1.2 after closing/reviewing C2.4.1.1. Do not patch the main Expr_Builtin proof before C2.4.1.3/C2.4.1.4.

## Do Not Retry
- Proving that materialized `Value (ArrayV (SArrayV _))` fixed arrays are unreachable from well-typed expressions.: False: E0796 proves reachability via a singleton local `Name` under `env_consistent`, `state_well_typed`, `context_well_typed`, `accounts_well_typed`, and `functions_well_typed`.
  - evidence: episode:E0796
  - evidence: tool_output:TO_type_system_rewrite-20260522T073012Z_m42855_t001
- Continuing the main `eval_all_type_sound_mutual[Expr_Builtin]` Len proof before repairing `toplevel_array_length` and proving the boundary lemma.: The old main-goal TypeError branch is semantically real under current definitions; tactics cannot refute it.
  - evidence: episode:E0794
  - evidence: episode:E0796
  - evidence: tool_output:TO_type_system_rewrite-20260522T073012Z_m42857_t001
- Leaving old local theorems named `...type_error...probe` as source obligations after the definition repair.: They describe the old buggy behavior and should become false once C2.4.1.1 is implemented; C2.4.1.2 owns removing/replacing them.
  - evidence: tool_output:TO_type_system_rewrite-20260522T073012Z_m42857_t001
  - evidence: source:semantics/prop/vyperTypeStmtSoundnessScript.sml:7674
- Using the static fixed-array bound `n` for `SArrayV` length in `toplevel_array_length`.: The runtime `Value (ArrayV (SArrayV sparse))` case does not carry `n`; PLAN authorizes `&LENGTH sparse` unless a repository convention says otherwise.
  - evidence: tool_output:TO_type_system_rewrite-20260522T073012Z_m42857_t001

## Reflection
### Tunnel Vision Check
- Outside-the-box approach now authorized: change the executable semantics of `Len` for materialized static arrays, rather than adding stronger proof invariants.
- We were optimizing the wrong theorem when trying to close `Expr_Builtin` directly; the definition is the right abstraction boundary.
- The PLAN decomposition is now correct: small executable repair, remove stale diagnostics, prove boundary lemma, then integrate.
- Do not retry tactics in the main resume until the boundary lemma exists. If proof becomes hard again, suspect the helper statement/interface, not the goal tactics.
- A fresh expert should first question whether `&LENGTH sparse` is semantically the right length for sparse static arrays; the PLAN chose it because no static bound is available in `Value (ArrayV (SArrayV sparse))` at `toplevel_array_length`.

### What Went Wrong
- The prior proof path assumed the Len TypeError branch was a missing helper, but E0796 proved a concrete reachable counterexample: a local `Name` expression of fixed-array type can evaluate to `Value (ArrayV (SArrayV []))`, and old `toplevel_array_length_def` returns `Error (TypeError "toplevel_array_length")` for that value under full runtime invariants.
- The theorem was not tactically stuck; the executable semantics omitted a runtime representation admitted by the type system. Continuing inside the large `Expr_Builtin` resume was optimizing the wrong layer.
- Current source has diagnostic local probe theorems for the old bug in `vyperTypeStmtSoundnessScript.sml`; after repairing `toplevel_array_length`, at least the TypeError probe is intentionally false and must be removed/replaced under C2.4.1.2.

### Ignored Signals
- The all-sized-values boundary failure from E0794 already showed `SArrayV` was the suspicious case; the important question was reachability, not another case split in the main theorem.
- The local `Name` path was enough: no array literal, ABI machinery, or realistic contract setup was needed.
- The working tree contains many pre-existing untracked test files and dirty plan/state/dossier files; do not stage them accidentally.

### Strategy Adjustments
- Follow the replacement PLAN exactly: C2.4.1.1 definition repair, C2.4.1.2 cleanup of old probes, C2.4.1.3 boundary lemma, C2.4.1.4 integration in `Expr_Builtin`.
- For C2.4.1.1, implement the semantic fix in `semantics/vyperStateScript.sml`, not as a proof workaround in statement soundness.
- For later C2.4.1.3, state the no-TypeError boundary at the typed runtime-value level so the main theorem can use it directly at the old FAIL_TAC site.

### Oracle Feedback
- Strategist accepted E0796 and replaced the unprovability gate with a repair subtree. Key decision: support `Value (ArrayV (SArrayV sparse))` in `toplevel_array_length` rather than trying to exclude it.
- Oracle explicitly warned not to leave old counterexample probes as current source obligations after the definition repair.
- Oracle guidance says use `&LENGTH sparse` as the available runtime length convention unless repository evidence dictates otherwise; do not use the static fixed bound because it is not carried by `SArrayV` in this function.

## Evidence Pointers
- episode:E0796 - proved reachable full Len TypeError counterexample under full runtime invariants.
- tool_output:TO_type_system_rewrite-20260522T073012Z_m42855_t001 - holbuild accepted both C2.4.1.b probe theorems and then failed only at the known main Expr_Builtin FAIL marker.
- tool_output:TO_type_system_rewrite-20260522T073012Z_m42857_t001 - strategist review replaced the gate with repair subtree C2.4.1.1--C2.4.1.4.
- tool_output:TO_type_system_rewrite-20260522T073012Z_m42859_t004 - current PLAN frontier/active component is C2.4.1.1.
- source:semantics/vyperStateScript.sml:662 - `toplevel_array_length_def` currently has materialized DynArray/Tuple/Bytes/String cases and catch-all TypeError; add SArrayV before catch-all.
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:7674 - old diagnostic probes currently live before `Resume eval_all_type_sound_mutual[Expr_Builtin]`.
