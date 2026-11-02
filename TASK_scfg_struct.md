# TASK: SimplifyCFG structural obligations

## Meta
Status: planned
Priority: P1
Created: 2026-11-02
Location: venom/passes/simplify_cfg/simplifyCfgCorrectnessScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem simplify_cfg_establishes_all_reachable:
  ∀func. wf_function func ⇒ all_reachable (simplify_cfg_fn func)

Theorem simplify_cfg_preserves_ssa_form:
  ∀func. ssa_form func ∧ wf_function func ⇒ ssa_form (simplify_cfg_fn func)

Theorem simplify_cfg_preserves_wf_function:
  ∀func. wf_function func ⇒ wf_function (simplify_cfg_fn func)

Theorem simplify_cfg_preserves_wf_ssa:
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\ first_block_no_preds fn /\
  EVERY (\inst. inst.inst_opcode <> PHI) (HD fn.fn_blocks).bb_instructions ==>
  wf_ssa (simplify_cfg_fn fn)

Theorem simplify_cfg_preserves_defs_reach_uses:
  wf_function fn /\ fn_inst_wf fn /\ fn_shape_ok fn /\ first_block_no_preds fn /\
  simplify_cfg_fn_ok fn ==>
  fn_defs_reach_uses (simplify_cfg_fn fn)

Theorem simplify_cfg_phi_two_pairs:
  wf_function fn /\ fn_inst_wf fn ==>
  !inst. MEM inst (fn_insts (simplify_cfg_fn fn)) /\ inst.inst_opcode = PHI ==>
         2 <= LENGTH (phi_pairs inst.inst_operands)

Theorem simplify_cfg_jnz_targets_distinct:
  wf_function fn /\ fn_shape_ok fn /\
  (!inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = JNZ ==>
          ?c t f. inst.inst_operands = [c; Label t; Label f] /\ t <> f) ==>
  !inst. MEM inst (fn_insts (simplify_cfg_fn fn)) /\ inst.inst_opcode = JNZ ==>
         ?c t f. inst.inst_operands = [c; Label t; Label f] /\ t <> f
```

Supporting definitions (do not change them): the pass in
`venom/passes/simplify_cfg/defs/simplifyCfgDefsScript.sml`; `wf_function`,
`ssa_form`, `wf_ssa`, `fn_defs_reach_uses` in `venom/defs/venomWfScript.sml`;
`fn_shape_ok`, `first_block_no_preds` (rg); `simplify_cfg_fn_ok`,
`canon_jnz_inst` in the pass's defs; `all_reachable` (rg
`all_reachable_def`).

**Do not modify these statements.** Prove them as-is, or produce a counterexample.

## Completion Criteria

1. The seven theorems build with no cheat; put helper lemmas in a new
   theory under venom/passes/simplify_cfg/proofs/ and import it.
2. Leave `simplify_cfg_pass_correct` and venom/passes/simplify_cfg/proofs/simplifyCfgProofScript.sml
   alone (another run proves them). Do not edit `venom/compiler/` or any
   definition.
3. No duplicate or near-duplicate lemmas; reuse simplifyCfgLabelProps.

**If a theorem is false as stated:** produce a HOL4 counterexample
(`EVAL` on a concrete function), state the tightest sufficient fix, and
stop. Do NOT silently weaken the statement.

## Build

```
holbuild --max-heap 7000 -j4 build simplifyCfgCorrectnessTheory
```

## Background

SimplifyCFG (Vyper's `simplify_cfg.py`) removes unreachable blocks,
merges a block into its sole predecessor, bypasses single-JMP blocks,
renames labels and fixes PHIs, iterated to a fixpoint (bounded by the
block count).  These are the structural facts later passes assume of
its output.

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
| A sibling pass proof of the same shape | venom/compiler/o1ContractSueScript.sml | (semantic, less relevant here) |
| Older cfg pass proofs | venom/passes/cfg_normalization/ | block-level simulation patterns |

## Notes

- The pass definitions changed since an earlier run of this task:
  `do_merge_jump` now canonicalizes `jnz c @L @L` to `jmp @L`
  (`canon_jnz_inst`) and, when the bypass target is the source block
  itself, applies the PHI update to it too.  `simplify_cfg_fn_ok` was
  restated.  simplifyCfgLabelProps was adapted and builds.
- simplifyCfgLabelProps may be edited (e.g. to export a `[local]`
  lemma); keep its existing theorems' statements.

- `simplify_cfg_fn fn = FST (simplify_cfg_fn_with_labels fn)`.
- `first_block_no_preds` keeps the entry block from ever being merged
  into a predecessor or bypassed.
