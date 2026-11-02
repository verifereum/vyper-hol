# TASK: SimplifyCFG meets the step part of the O1 pass contract

## Meta
Status: planned
Priority: P0
Created: 2026-11-02
Location: venom/compiler/o1ContractSimplifyCfgStepScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem simplify_cfg_step_contract:
  o1_step_contract rpolicy (CFP_Simple VP_SimplifyCFG)
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `simplify_cfg_step_contract` builds with no cheat, and so does every
   theory you add or change.
2. No duplicate or near-duplicate lemmas.
3. The cheated theorems in
   `venom/passes/simplify_cfg/simplifyCfgCorrectnessScript.sml`
   (`simplify_cfg_preserves_wf_function`, `simplify_cfg_phi_two_pairs`,
   `simplify_cfg_jnz_targets_distinct`, ...) are proved by another run:
   you may use them, but do not edit or prove them, and do not edit any
   definition or anything in `venom/compiler/` except
   `o1ContractSimplifyCfgStepScript.sml`.  New lemmas about the pass go in
   `venom/passes/simplify_cfg/proofs/` (a new theory if needed) or in the
   step script.

**If the theorem is false as stated:** produce a HOL4 counterexample
(`EVAL` on a concrete function), state the tightest sufficient fix, and
stop. Do NOT silently weaken the statement.

## Build

```
holbuild --max-heap 7000 -j4 build o1ContractSimplifyCfgStepTheory
```

## Background

The step part of the contract (`o1_step_contract_def`,
`venom/compiler/o1PassContractScript.sml`) says one run of the pass on a
function `fn` of the observed context keeps the O1 function shape
(`o1_fn_shape`), makes only fresh labels and instruction ids
(`fresh_names_ok`), maps only labels the output lost, never the entry
(`label_map_sources_ok`), and keeps the supply well formed.
`fn_pass_step_def` gives `lookup_unique_function fn.fn_name
observed.cu_context.ctx_functions = SOME fn`, so `o1_ctx_shape` of the
observed context gives `o1_fn_shape` of `fn` itself.  The dispatcher
(`venom/defs/venomPassDispatcherScript.sml`) runs
`simplify_cfg_fn_with_labels fn` and keeps the supply.

SimplifyCFG creates no labels and no instruction ids: it removes
unreachable blocks, merges a block into its sole predecessor, bypasses
jump-only blocks (canonicalizing `jnz c @L @L` to `jmp @L`), and fixes
PHIs in place (a PHI left with one pair becomes an ASSIGN, with none a
NOP; the entry block has no predecessors, so its PHIs become NOPs).  The
entry block has no predecessors (`first_block_no_preds`), so it is never
merged or bypassed and stays first.  The input need not be SSA and may
contain PHIs.

A statement check (by reading, not built) found every conjunct provable;
the bulk of the work is two `collapse_dfs` invariants nobody has stated
yet: (A) the entry keeps no predecessors and stays at the head of the
block list; (B) after the DFS no terminator or PHI names a removed label,
and every PHI's labels are among its block's predecessors.

## Domain Constraints

- holbuild only; never raise the tactic timeout; no `TRY`/`ORELSE`
  around metis or other search; no `let` in statements.
- Proofs under ~50 lines each; split into helper lemmas.
- Read `AGENTS.md` at the project root.

## Available Resources

| Resource | Location | Description |
|---|---|---|
| Contract | venom/compiler/o1PassContractScript.sml | `o1_step_contract`, `o1_fn_shape`, `fresh_names_ok`, `label_map_sources_ok`, `fn_pass_step`, `first_block_no_phi`, `fn_invoke_ok`, `fn_label_refs_ok`, entry clauses |
| A proved step contract of another pass | git show origin/bot/opus/seq-511-lower-dload:venom/compiler/o1ContractLowerDloadScript.sml | same conclusion, different pass; structure to imitate |
| Pass definitions | venom/passes/simplify_cfg/defs/simplifyCfgDefsScript.sml | `simplify_cfg_fn_with_labels`, `collapse_dfs`, `fix_all_phis`, `fix_phi_inst`, `canon_jnz_inst`, `merge_blocks`, `try_bypass` |
| Structural lemmas (proved) | venom/passes/simplify_cfg/proofs/simplifyCfgLabelPropsScript.sml | `simplify_cfg_fn_with_labels_transition` (label map sources), `*_invoke_subset`, `*_no_new_call_edges`, `*_metadata`, `collapse_dfs_result` and joint invariants |
| Structural obligations (cheated, proved elsewhere) | venom/passes/simplify_cfg/simplifyCfgCorrectnessScript.sml | `simplify_cfg_preserves_wf_function`, `simplify_cfg_phi_two_pairs`, `simplify_cfg_jnz_targets_distinct` |
| Shape | venom/defs/ (rg `fn_shape_ok_def`, `inst_shape_ok_def`, `label_positions_ok_def`, `opaque_use_ok_def`, `first_block_no_preds_def`) | |
| CFG | venom/defs/cfgTransformScript.sml, venom/defs/cfgWfScript.sml | `bb_succs`, `pred_labels`, `subst_block_labels_fn` |
| Well-formedness | venom/defs/venomWfScript.sml | `wf_function`, `fn_inst_wf`, `inst_wf` |
| Older SimplifyCFG proof (reference only, never landed) | git ref `refs/scfg/pr307` | `simplifyCfgWf*`, collapse lemmas; port ideas, don't copy blindly |

## Notes

- `simplify_cfg_fn fn = FST (simplify_cfg_fn_with_labels fn)`.
