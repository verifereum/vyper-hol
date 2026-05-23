# STATE_type_system_rewrite
Updated: 2026-05-23

## Cursor
- component: C2.4.1.4
- status: ready
- active_file: semantics/prop/vyperTypeBuiltinsScript.sml
- next_action: First inspect git status/diff: C2.4.1.3 cleanup and DOSSIER are reviewed but uncommitted; if still only those stable tracked diffs, commit them before proof work. Then continue active component C2.4.1.4 by adding a Len typed-runtime no-TypeError boundary near `Len_result_fits_uint256`/`Len_builtin_sound` in `vyperTypeBuiltinsScript.sml`. Suggested theorem: from `well_typed_builtin_app ty Len [arg_ty]`, `evaluate_type tenv arg_ty = SOME arg_runtime_tv`, `well_formed_type_value arg_runtime_tv`, `toplevel_value_typed arg_tv arg_runtime_tv`, and `toplevel_array_length cx arg_tv st = (INR (Error (TypeError err)), st')`, prove `F` (or equivalently contradiction/no TypeError). Keep `toplevel_array_length_def` unfolding inside this boundary only.
- expected_goal_shape: The last verified downstream failure is the planned `Expr_Builtin` Len branch: assumptions include `well_typed_builtin_app ty Len (MAP expr_type es)`, `expr_result_typed env (HD es) arg_tv`, and `toplevel_array_length cx arg_tv arg_st = (INR len_exn,arg_st)`, goal `∀msg. len_exn ≠ Error (TypeError msg)`. For C2.4.1.4, expect smaller boundary subgoals from cases on Len-eligible `arg_ty`/`arg_tv`; after C2.4.1.1, materialized `SArrayV` should simplify to success, not TypeError.
- verify_with: holbuild(targets=["vyperTypeBuiltinsTheory"], timeout=600) for the boundary if placed in builtins; then holbuild(targets=["vyperTypeStmtSoundnessTheory"], timeout=600) should still stop at the Expr_Builtin FAIL_TAC until C2.4.1.5 integrates the boundary.

## If This Fails
- If the boundary proof needs large unfolding or brittle assumptions, checkpoint_progress for C2.4.1.4 with the exact holbuild goal and ask plan_oracle only after a terminal stuck/abandoned closure. If `vyperTypeStmtSoundnessTheory` fails before the known Expr_Builtin Len FAIL_TAC, inspect whether the uncommitted cleanup or previous commits were lost before changing proofs.

## Do Not Retry
- Proving materialized `Value (ArrayV (SArrayV _))` fixed arrays are unreachable from well-typed expressions.: False; E0796 proved reachability via a singleton local `Name` under full runtime invariants.
  - evidence: episode:E0796
  - evidence: tool_output:TO_type_system_rewrite-20260522T073012Z_m42855_t001
- Leaving or recreating local facts that fixed-array `SArrayV` Len returns `Error (TypeError "toplevel_array_length")`.: Definition repair C2.4.1.1 makes that behavior false; C2.4.1.3 deleted the stale probes and audit found no remaining names.
  - evidence: episode:E0801
  - evidence: tool_output:TO_type_system_rewrite-20260522T073012Z_m42907_t001
- Inlining the full `toplevel_array_length_def` case split directly in `eval_all_type_sound_mutual[Expr_Builtin]`.: PLAN assigns this to C2.4.1.4 as a boundary lemma, then C2.4.1.5 should consume it; duplicating in the consumer repeats the earlier abstraction mistake.
  - evidence: plan:C2.4.1.4
  - evidence: episode:E0794
- Using the static fixed-array bound `n` as the returned length for materialized `SArrayV` in `toplevel_array_length`.: The runtime value carries only `sparse`; the accepted repair returns `&LENGTH sparse` and then bounds it with `sparse_has_type_length`.
  - evidence: episode:E0797
  - evidence: episode:E0800

## Reflection
### Tunnel Vision Check
- Outside-the-box option already used: change executable Len semantics for materialized static arrays. The remaining work should not revisit unreachability or statement weakening.
- Check whether placing the boundary in `vyperTypeBuiltinsScript.sml` creates any dependency friction; if so, local placement in `vyperTypeStmtSoundnessScript.sml` is allowed by PLAN, but avoid duplicating the case split in the resume.
- A fresh expert should first question whether the boundary theorem’s conclusion matches the old FAIL_TAC use site exactly; if it requires too much manual instantiation in C2.4.1.5, restate it before proving more.
- If C2.4.1.4 becomes hard, suspect the helper statement/interface, not tactics. The theorem should be a small definition-boundary case split after C2.4.1.1/C2.4.1.2.

### What Went Wrong
- Earlier sessions optimized the large `Expr_Builtin` resume while the executable semantics omitted a runtime representation admitted by typing. E0796 proved the reachable counterexample; C2.4.1.1 repaired the definition and C2.4.1.2 repaired the exposed builtin length bound.
- After the definition repair, the old cleanup component was initially misordered: `vyperTypeStmtSoundnessTheory` failed first in `Len_result_fits_uint256`, not at stale probes. The strategist accepted E0798 and inserted the builtin repair before cleanup.
- Current source still has a partial `Expr_Builtin` proof skeleton with a `FAIL_TAC` in the Len TypeError path and another for non-Len. That is intentional: C2.4.1.4 should add a boundary lemma before C2.4.1.5 integrates it.

### Ignored Signals
- The all-sized-values helper failure in E0794 already showed `SArrayV` needed definition-level attention; further inline case splitting in the consumer proof was not the right abstraction.
- A downstream build after C2.4.1.1 was essential: it exposed `Len_result_fits_uint256` fallout before stale probe cleanup could be verified.
- There are many pre-existing untracked test/probe files; do not stage them. Current stable tracked source/dossier changes from C2.4.1.3 were not committed before handoff.

### Strategy Adjustments
- Work at the boundary level: put the no-TypeError theorem near `Len_result_fits_uint256`/`Len_builtin_sound` or another builtin-facing location, and keep `toplevel_array_length_def` unfolding out of the statement mutual proof.
- Before new proof edits, preserve the reviewed C2.4.1.3 cleanup by committing only `semantics/prop/vyperTypeStmtSoundnessScript.sml` and task-owned dossier/plan state that actually changed; never `git add -A`.
- For the boundary lemma, use case analysis over `well_typed_builtin_app_def`, `evaluate_type_def`, `toplevel_value_typed_def`, and repaired `toplevel_array_length_def`. Do not attempt to prove materialized `SArrayV` unreachable.

### Oracle Feedback
- Strategist’s key insight held: support `Value (ArrayV (SArrayV sparse))` in `toplevel_array_length` and repair the builtin Len boundary, rather than weakening public soundness.
- Strategist initially missed the immediate `Len_result_fits_uint256` fallout; E0798 corrected the plan and the `sparse_has_type_length` guidance proved effective in E0800.
- C2.4.1.3 cleanup was accepted; no local theorem should now claim fixed-array Len returns `TypeError "toplevel_array_length"`.

## Evidence Pointers
- episode:E0800 - repaired `Len_result_fits_uint256` for materialized static arrays; `vyperTypeBuiltinsTheory` builds
- tool_output:TO_type_system_rewrite-20260522T073012Z_m42897_t001 - clean `vyperTypeBuiltinsTheory` build after the Len bound repair
- episode:E0801 - removed stale fixed-array Len TypeError probes and grep-audited source
- tool_output:TO_type_system_rewrite-20260522T073012Z_m42907_t003 - downstream build now reaches the planned Expr_Builtin Len TypeError-path FAIL_TAC
- tool_output:TO_type_system_rewrite-20260522T073012Z_m42913_t004 - current PLAN frontier/active component is C2.4.1.4
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:7732 - current known FAIL_TAC site for later integration
