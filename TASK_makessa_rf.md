# TASK: MakeSSA keeps revert-forward pairs

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: venom/passes/make_ssa/proofs/makeSsaCurrentRevertForwardScript.sml (project root: this directory)

## Theorem Statement (FROZEN)

```sml
Theorem make_ssa_current_fn_revert_forward_at:
  make_ssa_input_ok fn /\ fn_inst_wf fn /\ wf_function fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (fn',s') /\
  lookup_block l fn.fn_blocks = SOME bb /\
  lookup_block l fn'.fn_blocks = SOME bb' /\
  revert_forward_at bb k ==>
  LENGTH bb.bb_instructions <= LENGTH bb'.bb_instructions /\
  revert_forward_at bb'
    (k + (LENGTH bb'.bb_instructions - LENGTH bb.bb_instructions))
```

Definitions: `make_ssa_current_fn` and its parts in `venom/passes/make_ssa/defs/makeSsaCurrentDefsScript.sml` (plus `insert_phi_at_block`, `compute_defs`, `insert_phis_for_var_supply` in `venom/passes/make_ssa/defs/makeSsaDefsScript.sml` / the same file); `revert_forward_at`, `revert_forward_pair`, `same_after_assigns`, `step_back_assign`, `resolve_block_assigns` in `venom/codegen/defs/contextCodegenRelScript.sml`; `make_ssa_input_ok`, `first_block_no_phi` in `venom/compiler/o1PassContractScript.sml`; `first_block_no_preds` in `venom/compiler/unitShapeDefsScript.sml`; `ir_supply_covers_fn`, `ir_supply_inst_ok`, `fresh_ir_var` under `venom/` (grep `Definition ir_supply_covers_fn_def`).

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

## Completion Criteria

1. The build below passes with zero CHEAT warnings in `makeSsaCurrentRevertForwardTheory`, and nothing it depends on is admitted (see Domain Constraints).
2. Helper lemmas go in new theories under `venom/passes/make_ssa/proofs/` (or in `makeSsaCurrentRevertForwardScript.sml`); each exists once in its most general form.
3. No change to any existing theory.

**If the theorem is false as stated:** produce a HOL4 counterexample (EVAL on concrete values of `make_ssa_current_fn`), state the tightest sufficient fix, and do NOT weaken the statement.

## Build

```
holbuild -j4 build makeSsaCurrentRevertForwardTheory
```

Run from this directory (the one with `holproject.toml`).

## Background

This is the static half of MakeSSA's revert-forward frame simulation (`frame_sim_rf` in `venom/compiler/o1PassLiftScript.sml`): a revert forwarding (`in_revert_forward`, a RETURNDATACOPY of a callee's revert data followed by a REVERT of it) in the input function must still be one at the corresponding instruction of the output, so that an output state outside every revert forwarding corresponds to an input state outside one. MakeSSA inserts pruned PHIs at the front of blocks, renames along the dominator tree (first definition keeps its spelling, later ones get fresh supply names), renames existing PHI operands per predecessor edge, and, when the input had PHIs, cleans up degenerate PHIs within the leading PHI prefix.

## Domain Constraints

- Use holbuild only (no Holmake, no REPL sessions). Default tactic timeout; never raise it.
- No `cheat` in the result. No `TRY`/`ORELSE` around metis or other search.
- No `let` in theorem statements.
- Don't use the admitted theories on this branch as ancestors: `makeSsaCurrentWfSsaTheory`, `makeSsaCurrentSimTheory`, `makeSsaCurrentInputOkTheory`, `makeSsaCurrentNonDegenerateTheory`, `makeSsaCurrentFrameRfTheory` (their theorems are cheated). Proved facts from the reference branches below may be ported (copied with their proofs) into new theories here.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| MakeSSA definitions | `venom/passes/make_ssa/defs/makeSsaCurrentDefsScript.sml` | the pass under proof; its own small lemmas at the end (labels, ids, vars, length of the cleaned prefix) |
| Proved basic MakeSSA facts | `venom/passes/make_ssa/proofs/makeSsaCurrentPropsScript.sml`, `makeSsaCurrentInductScript.sml` | proved, usable as ancestors |
| Revert-forward definitions | `venom/codegen/defs/contextCodegenRelScript.sml` lines ~285-380 | |
| SUE's version of this fact | `venom/compiler/o1ContractSueScript.sml` (`sue_segments_supply_revert_forward_pair`, `sue_frame_align_rf_observations`) | how another pass proved revert-forward preservation |
| Reference: MakeSSA static machinery (proved, older base) | `alan-ref/makessa3/venom/passes/make_ssa/proofs/` | many `makeSsaCurrent*` theories: rename traces (`makeSsaCurrentRenameTraceScript.sml`, `makeSsaCurrentTreeTraceScript.sml`), block shape and positions (`makeSsaCurrentPhaseShapeScript.sml`, `makeSsaCurrentOrdinaryIdsScript.sml`, `makeSsaCurrentCleanupShapeScript.sml`, `makeSsaCurrentFinalBlockScript.sml`), structural certificate (`makeSsaCurrentCertificateScript.sml`), output names (`makeSsaCurrentOutputNamesScript.sml`). Reading only; a file there with an unfinished proof is not proved. Port what you need. |
| Reference: proved `make_ssa_current_fn_wf_ssa` | `alan-ref/makessa-wf/venom/passes/make_ssa/proofs/makeSsaCurrentWfSsaScript.sml` | fresh-name/distinct-output facts about the renaming; port what you need |

## Notes

- `makeSsaCurrentDefsScript.sml` in both `alan-ref/*` trees is byte-identical to this branch's; other theories there (e.g. `contextCodegenRelScript.sml`) differ, so use this branch's revert-forward definitions.
