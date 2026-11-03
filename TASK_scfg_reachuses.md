# TASK: SimplifyCFG structural obligation: simplify_cfg_preserves_defs_reach_uses

## Meta
Status: planned
Priority: P1
Created: 2026-11-03
Location: venom/passes/simplify_cfg/simplifyCfgCorrectnessScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem simplify_cfg_preserves_defs_reach_uses:
  wf_function fn /\ fn_inst_wf fn /\ fn_shape_ok fn /\ first_block_no_preds fn /\
  simplify_cfg_fn_ok fn ==>
  fn_defs_reach_uses (simplify_cfg_fn fn)
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

Supporting definitions (do not change them): the pass in
`venom/passes/simplify_cfg/defs/simplifyCfgDefsScript.sml`; `wf_function`,
`ssa_form`, `wf_ssa`, `fn_defs_reach_uses` in `venom/defs/venomWfScript.sml`;
`fn_shape_ok`, `first_block_no_preds` (rg); `simplify_cfg_fn_ok`,
`canon_jnz_inst` in the pass's defs; `all_reachable` (rg `all_reachable_def`).

## Completion Criteria

1. `simplify_cfg_preserves_defs_reach_uses` builds with no cheat. Replace only its own `cheat` in
   simplifyCfgCorrectnessScript.sml. Put new helper lemmas in a new theory
   `venom/passes/simplify_cfg/proofs/simplifyCfgReachusesScript.sml` and add it
   to simplifyCfgCorrectness's Ancestors.
2. Leave the other theorems in simplifyCfgCorrectnessScript.sml (other runs prove
   them), `simplify_cfg_pass_correct`, simplifyCfgProofScript.sml,
   `venom/compiler/` and every definition alone. Don't edit existing proof theories
   other than to drop `[local]` from a lemma you need, with one exception
   (amended 2026-11-03 by the task owner): you may move `inst_wf_subst_label_inst`
   and the private helpers it strictly needs out of cfgNormProofScript.sml into a
   lightweight proof theory that doesn't depend on execEquivProofs (next to the
   definitions it is about), and update its existing consumers to use it there.
   Move, don't copy: no duplicate. Leave execEquivProofs alone.
3. No duplicate or near-duplicate lemmas: reuse what's already proved.

**If the theorem is false as stated:** produce a HOL4 counterexample
(`EVAL` on a concrete function), state the tightest sufficient fix, and stop.

## Build

```
holbuild --max-heap 7000 -j2 build simplifyCfgCorrectnessTheory
```

## Background

SimplifyCFG (Vyper's `simplify_cfg.py`) removes unreachable blocks,
merges a block into its sole predecessor, bypasses single-JMP blocks
(`do_merge_jump`, which canonicalizes `jnz c @L @L` to `jmp @L` via
`canon_jnz_inst`), renames labels and fixes PHIs, iterated to a fixpoint
(bounded by the block count). `simplify_cfg_fn fn = FST (simplify_cfg_fn_with_labels fn)`.
`first_block_no_preds` keeps the entry block from ever being merged into a
predecessor or bypassed.

## Domain Constraints

- holbuild only; never raise the tactic timeout; no `TRY`/`ORELSE`
  around metis or other search; no `let` in statements.
- Proofs under ~50 lines each; split into helper lemmas.
- Read `AGENTS.md` at the project root.

## Available Resources

| Resource | Location | Description |
|---|---|---|
| Pass definitions | venom/passes/simplify_cfg/defs/simplifyCfgDefsScript.sml | `remove_unreachable_blocks`, `fix_phi_inst`, `fix_all_phis`, `can_merge_blocks`, `merge_blocks`, `try_bypass`, `do_merge_jump`, `collapse_dfs`, `simplify_cfg_round_with_labels`, `simplify_cfg_iter_with_labels` |
| Structural lemmas | venom/passes/simplify_cfg/proofs/simplifyCfgLabelPropsScript.sml | collapse_dfs invariant composition (`collapse_dfs_result`, `*_joint`), label-map chronology, label/inst subset facts |
| Earlier structural work | venom/passes/simplify_cfg/proofs/simplifyCfg{Struct,PhiRepair,PhiPreds,Dataflow,ChainDataflow,RepairDataflow,BypassDataflow}Script.sml | a previous run's checked lemmas: per-step preservation (merge, bypass, unreachable removal, phi repair), predecessor facts, def-use transport |
| CFG transforms | venom/defs/cfgTransformScript.sml | `bb_succs`, `block_preds`, `pred_labels`, `subst_block_labels_fn`, `reachable` |
| CFG lemmas | venom/defs/cfgWfScript.sml, venom/analysis/cfg/proofs/cfgHelpersScript.sml, venom/analysis/cfg/cfgAnalysisPropsScript.sml | |
| Well-formedness | venom/defs/venomWfScript.sml | |
| Dominator facts | venom/analysis/dominators/proofs/dominatorProofsScript.sml | |

## Notes

- A previous run built most of the def-use transport for this theorem: per-step
  transport through unreachable-block removal, PHI repair and chain merge
  (simplifyCfgDataflow, simplifyCfgChainDataflow, simplifyCfgRepairDataflow,
  simplifyCfgPhiPreds), and a partial bypass (`do_merge_jump`) transport in
  simplifyCfgBypassDataflowScript.sml. Its last unbuilt edit was in
  `do_merge_jump_def_on_all_paths_endpoint`. Continue from those theories rather than
  starting over; extend simplifyCfgBypassDataflow or put new lemmas in the new theory.
- `simplify_cfg_preserves_wf_ssa` is false as stated (simplifyCfgStalePhiProbe) and is
  restated elsewhere; don't use it. The *Probe* theories are diagnostics; ignore them.
