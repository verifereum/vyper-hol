# TASK: SimplifyCFG preserves a function's runs and reachable states

## Meta
Status: planned
Priority: P0
Created: 2026-11-02
Location: venom/passes/simplify_cfg/proofs/simplifyCfgProofScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem simplify_cfg_fn_correct:
  wf_function fn /\ fn_inst_wf fn /\ fn_shape_ok fn /\ first_block_no_preds fn /\
  simplify_cfg_fn_ok fn ==>
  fn_bisim fn (simplify_cfg_fn fn)

Theorem simplify_cfg_frame_sim:
  ctx_bisim C C' /\
  wf_function fn /\ fn_inst_wf fn /\ fn_shape_ok fn /\ first_block_no_preds fn /\
  simplify_cfg_fn_ok fn ==>
  frame_sim L C C' fn (simplify_cfg_fn fn)
```

Supporting definitions (do not change them):
- `simplify_cfg_fn_ok_def`, `simplify_cfg_fn_def` and the whole pass:
  `venom/passes/simplify_cfg/defs/simplifyCfgDefsScript.sml`
- `fn_bisim_def`, `fn_entry_state_def`, `frame_result_rel_def`, `ctx_bisim_def`,
  `frame_reach` (inductive), `frame_sim_def`, `mem_corr_def`, `call_corr_def`:
  `venom/compiler/o1PassLiftScript.sml`

**Do not modify these statements.** Prove them as-is, or produce a counterexample.

(*
 ************************************************************
 * DO NOT START THIS PROOF until you have finished and
 * validated ALL the machinery you will need for it.
 * Building generic lemmas about the pass's sub-steps
 * (unreachable-block removal, PHI fixup, merge, bypass,
 * label substitution, the iteration) IS in scope; put them
 * in new theories under venom/passes/simplify_cfg/proofs/.
 ************************************************************
 *)

## Completion Criteria

1. `simplify_cfg_fn_correct` and `simplify_cfg_frame_sim` build with no
   cheat, and so does every theory they depend on that you add or change.
2. `simplifyCfgCorrectnessTheory` (re-exports it as
   `simplify_cfg_pass_correct`) builds.
3. No duplicate or near-duplicate lemmas.
4. Leave the other obligations in simplifyCfgCorrectnessScript.sml alone
   (another run proves them). Do not edit `venom/compiler/` or any
   definition.

**If the theorem is false as stated:** produce a HOL4 counterexample
(`EVAL` on a concrete function and state), state the tightest
sufficient fix, and stop. Do NOT silently weaken the statement.

## Build

```
holbuild --max-heap 7000 -j4 build simplifyCfgProofTheory simplifyCfgCorrectnessTheory
```

## Background

SimplifyCFG (Vyper's `simplify_cfg.py`) removes unreachable blocks,
merges a block into its sole predecessor, bypasses single-JMP blocks,
renames labels, and fixes PHIs whose predecessors changed (a PHI left
with one predecessor becomes an ASSIGN, with none a NOP), iterated to a
fixpoint.  `fn_bisim` says the output runs like the input from every
frame entry state, in any context, both directions, fuel existential.
`simplify_cfg_fn_ok` is the precondition that makes the PHI-to-ASSIGN
change, the dropped first-block PHIs and dropped `jnz %c @b @b`
conditions invisible; its comment explains each conjunct.  The theorem
feeds the O1 pass contract via `venom/compiler/o1PassLiftScript.sml`.
`frame_sim` says every state a frame of the output reaches (also on runs
that later fail) corresponds to one the input reaches from the same
entry state, with the same alloca frame and memory ranges, and an INVOKE
to an INVOKE of the same callee with the same arguments; `ctx_bisim C C'`
lets an INVOKE step in C' be matched in C (`ctx_bisim_step_inst`).

## Domain Constraints

- holbuild only; never raise the tactic timeout; no `TRY`/`ORELSE`
  around metis or other search; no `let` in statements.
- Proofs under ~50 lines each; split into helper lemmas.
- Read `AGENTS.md` at the project root.

## Available Resources

| Resource | Location | Description |
|---|---|---|
| Pass definitions | venom/passes/simplify_cfg/defs/simplifyCfgDefsScript.sml | `remove_unreachable_blocks`, `fix_phi_inst`, `fix_all_phis`, `can_merge_blocks`, `merge_blocks`, `try_bypass`, `collapse_dfs`, `simplify_cfg_round_with_labels`, `simplify_cfg_iter_with_labels` |
| Structural lemmas | venom/passes/simplify_cfg/proofs/simplifyCfgLabelPropsScript.sml | collapse_dfs invariant composition (`collapse_dfs_result`, `*_joint`), label-map chronology, label/inst subset facts |
| Executable checks | venom/passes/simplify_cfg/defs/simplifyCfgComputeScript.sml | |
| CFG transforms | venom/defs/cfgTransformScript.sml | `bb_succs`, `block_preds`, `pred_labels`, `subst_block_labels_fn`, `reachable` |
| CFG lemmas | venom/defs/cfgWfScript.sml, venom/analysis/cfg/proofs/cfgHelpersScript.sml, venom/analysis/cfg/cfgAnalysisPropsScript.sml | |
| Well-formedness | venom/defs/venomWfScript.sml | `wf_function`, `fn_inst_wf`, `def_available_at`, `fn_dominates`, `fn_reachable`, `fn_cfg_edge` |
| Dominator facts | venom/analysis/dominators/proofs/dominatorProofsScript.sml | |
| Semantics | venom/defs/venomExecSemanticsScript.sml | `run_blocks`, `eval_phis`, `resolve_phi`, `exec_block`, `step_inst`, `phi_prefix_length` |
| Semantics lemmas | venom/proofs/venomExecProofsScript.sml, venom/props/venomExecPropsScript.sml, venomInstProofs* (rg `Theory venomInstProofs`) | |
| Lift layer | venom/compiler/o1PassLiftScript.sml | `fn_bisim`, `frame_result_rel`, `execution_frame` use |
| A sibling pass proof of the same shape | venom/compiler/o1ContractSueScript.sml | SUE's `fn_bisim` statement |
| Older SimplifyCFG proof (reference only, older semantics, never landed) | git ref `refs/scfg/pr307`: `git show refs/scfg/pr307:venom/passes/simplify_cfg/proofs/<file>` | collapse/merge (`simplifyCfgCollapse*`), prev_bb (`simplifyCfgPrevBB`), step, wf (`simplifyCfgWf`), helpers; port ideas, don't copy |
| Older cfg pass proofs | venom/passes/cfg_normalization/ | block-level simulation patterns |

## Notes

- The pass definitions changed since an earlier run of this task:
  `do_merge_jump` now canonicalizes `jnz c @L @L` to `jmp @L`
  (`canon_jnz_inst`) and, when the bypass target is the source block
  itself, applies the PHI update to it too.  `simplify_cfg_fn_ok` was
  restated (its first conjunct: no PHI in the first block).  Recheck any
  lemma about `do_merge_jump` or `simplify_cfg_fn_ok` against the new
  definitions.

- `simplify_cfg_fn fn = FST (simplify_cfg_fn_with_labels fn)`.
- `first_block_no_preds` keeps the entry block from ever being merged
  into a predecessor or bypassed.
