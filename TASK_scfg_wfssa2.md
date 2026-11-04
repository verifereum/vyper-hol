# TASK: SimplifyCFG: repair simplify_cfg_preserves_wf_ssa on the current base

## Meta
Status: planned
Priority: P1
Created: 2026-11-03
Location: venom/passes/simplify_cfg/simplifyCfgCorrectnessScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem simplify_cfg_preserves_wf_ssa:
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\ fn_shape_ok fn /\
  first_block_no_preds fn /\ simplify_cfg_fn_ok fn ==>
  wf_ssa (simplify_cfg_fn fn)
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

Supporting definitions (do not change them): the pass in
`venom/passes/simplify_cfg/defs/simplifyCfgDefsScript.sml`; `wf_function`,
`ssa_form`, `wf_ssa`, `fn_defs_reach_uses` in `venom/defs/venomWfScript.sml`;
`fn_shape_ok`, `first_block_no_preds` (rg); `simplify_cfg_fn_ok`,
`canon_jnz_inst` in the pass's defs; `all_reachable` (rg `all_reachable_def`).

## Completion Criteria

1. `simplifyCfgCorrectnessTheory` builds with no cheat in
   `simplify_cfg_preserves_wf_ssa` (its proof is already there and uses
   `simplifyCfgWfssaTheory`). The other theorems of
   simplifyCfgCorrectnessScript.sml must keep building; leave their
   statements and proofs alone.
2. You may edit `venom/passes/simplify_cfg/proofs/simplifyCfgWfssaScript.sml`
   freely (and `simplifyCfgReachusesScript.sml` if it fails too), and add
   helper lemmas there. Leave every definition, `venom/compiler/`,
   simplifyCfgProofScript.sml and the other proof theories alone, except
   dropping `[local]` from a lemma you need.
3. No duplicate or near-duplicate lemmas: reuse what's already proved.

## What broke

simplifyCfgWfssaScript.sml was proved against an older `label_positions_ok`
(venom/compiler/unitShapeDefsScript.sml). Its JNZ arm now also requires
distinct targets: `(JNZ, [c; Label t; Label f]) => ~is_label_operand c /\ t <> f`,
and its CODECOPY arm is an equation `l = "runtime_begin"`. The build now
fails at `subst_label_inst_label_positions_ok` (a bare label substitution can
make a JNZ's two targets equal; `do_merge_jump` applies `canon_jnz_inst`
afterwards, so the composite step still keeps it), and probably at the
lemmas that carry `EVERY label_positions_ok (fn_insts fn)` through each
step. Restate or replace those helper lemmas as needed (e.g. carry only the
part of label positions the SSA proof uses, or prove preservation per pass
step including the canonicalization). simplifyCfgJnzdistScript.sml already
proves the pass keeps JNZ targets distinct; reuse it.

## Build

```
holbuild --gcthreads 1 --max-heap 7000 -j2 build simplifyCfgCorrectnessTheory
```

(`--gcthreads 1` works around a holbuild startup GC crash on this box;
the `holbuild` on PATH for this run already adds it.)

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

- This statement replaces an earlier one without `fn_shape_ok` and
  `simplify_cfg_fn_ok`, which was false: simplifyCfgStalePhiProbeScript.sml has the
  counterexample (a JNZ with a Label condition, which `fn_shape_ok`'s
  `label_positions_ok` now excludes; `simplify_cfg_fn_ok` includes the entry block
  having no PHI). The probe theories are diagnostics; ignore them otherwise.
- The previous run's PHI-repair and predecessor lemmas (simplifyCfgPhiRepair,
  simplifyCfgPhiPreds, simplifyCfgStruct) cover much of the PHI side.
