# TASK: SimplifyCFG's two runs meet the stage part of the O1 pass contract

## Meta
Status: planned
Priority: P0
Created: 2026-11-02
Location: venom/compiler/o1ContractSimplifyCfgScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem simplify_cfg_stage_pre_walk:
  !view. o1_stage_contract rpolicy (CFP_Simple VP_SimplifyCFG) view no_pre
           o1_pre_walk_inv o1_walk_src_inv

Theorem simplify_cfg_stage_walk:
  o1_run_contract rpolicy 5
```

Do not modify these statements. Prove them as-is, or produce a counterexample.

## Completion Criteria

1. `simplify_cfg_stage_pre_walk` and `simplify_cfg_stage_walk` build with
   no cheat, and so do the theories you add or change.
   `o1ContractTheoremsTheory` still builds.
2. No duplicate or near-duplicate lemmas.
3. Other runs prove, in parallel, theorems you may use as given (they are
   cheated now; their statements are fixed): `simplify_cfg_fn_correct`
   and `simplify_cfg_frame_sim`
   (`venom/passes/simplify_cfg/proofs/simplifyCfgProofScript.sml`), the
   obligations in `venom/passes/simplify_cfg/simplifyCfgCorrectnessScript.sml`,
   and `simplify_cfg_step_contract`
   (`venom/compiler/o1ContractSimplifyCfgStepScript.sml`).  Do not edit
   those files, any definition, or `o1PassContractScript.sml`/
   `o1PassLiftScript.sml`.  New lemmas go in
   `o1ContractSimplifyCfgScript.sml`, or, if they are about the pass
   alone (e.g. "no PHI in, no PHI out"), in a new theory under
   `venom/passes/simplify_cfg/proofs/`.

**If a theorem is false as stated:** produce a HOL4 counterexample
(`EVAL` on a concrete context and state), state the tightest sufficient
fix, and stop. Do NOT silently weaken the statement.

## Build

```
holbuild --max-heap 7000 -j4 build o1ContractSimplifyCfgTheory o1ContractTheoremsTheory
```

## Background

`o1_stage_contract_def` (`venom/compiler/o1PassContractScript.sml`): for
stage contexts `C`, `C'` with `ctx_pass_stage` (the pass applied to every
function, `LIST_REL` over `fn_pass_step`), `o1_ctx_shape C`, an initial
state `vs` with `o1_run_state_ok vs`, and the input row `I C vs`, show
`ctx_sim C C' vs vs` and the output row `I' C' vs`.

- Pre-walk run: `o1_pre_walk_inv` (raw memory invariant, every function
  `fn_defs_reach_uses` and PHI-free) to `o1_walk_src_inv` (raw memory
  invariant; every function `all_reachable`, `fn_defs_reach_uses`,
  `fn_phi_operands_single_def`, `fn_phis_cover_preds`).  The PHI
  conjuncts hold vacuously on the output because the pass adds no PHI to
  a PHI-free function.
- Run 5 (`o1_run_contract rpolicy 5`, the 5th entry of `o1_fn_passes` is
  SimplifyCFG): `o1_inv 5 = o1_inv 6 = o1_ssa_inv` (lowered memory
  invariant with some `eom`, `ctx_eom_bounded eom C`, every function
  `wf_ssa`).

The per-function theorems need `simplify_cfg_fn_ok fn`
(`simplifyCfgDefsScript.sml`).  It follows on the pre-walk from
`fn_defs_reach_uses` plus no PHI, and at run 5 from `first_block_no_phi`
(in `o1_fn_shape`) plus `wf_ssa`; neither implication is stated yet.
The lift layer (`venom/compiler/o1PassLiftScript.sml`) has the glue:
`fn_bisim_ctx_bisim` (per-function `fn_bisim` to `ctx_bisim`),
`ctx_bisim_ctx_sim` (to `ctx_sim`; needs no `IntRet` from the top-level
run, which the entry function's `entry_fn_no_return` in `o1_fn_shape`
should give), `frame_sim_mem_inv` with `mem_corr_closed_raw_mem_ok` and
`mem_corr_closed_lowered_mem_fact` (memory invariant transported along
`frame_sim`).  The pass keeps every function's name and entry label and
does not touch ALLOCA sizes, so `ctx_eom_bounded` should carry over.

## Domain Constraints

- holbuild only; never raise the tactic timeout; no `TRY`/`ORELSE`
  around metis or other search; no `let` in statements.
- Proofs under ~50 lines each; split into helper lemmas.
- Read `AGENTS.md` at the project root.

## Available Resources

| Resource | Location | Description |
|---|---|---|
| Contract | venom/compiler/o1PassContractScript.sml | stage contract, rows, `ctx_pass_stage`, `fn_pass_step`, `o1_fn_shape` |
| Lift layer | venom/compiler/o1PassLiftScript.sml | `fn_bisim`, `ctx_bisim`, `frame_sim`, lemmas above |
| Memory invariant | venom/compiler/unitMemInvScript.sml | `mem_inv`, `raw_mem_ok` |
| Pipeline use of the contracts | venom/compiler/o1PipelineComposeScript.sml | how the two theorems are consumed |
| Per-function theorems (cheated, proved elsewhere) | venom/passes/simplify_cfg/proofs/simplifyCfgProofScript.sml | `simplify_cfg_fn_correct` (fn_bisim), `simplify_cfg_frame_sim` |
| Structural obligations (cheated, proved elsewhere) | venom/passes/simplify_cfg/simplifyCfgCorrectnessScript.sml | all_reachable, wf_function, wf_ssa, fn_defs_reach_uses preservation |
| Pass definitions | venom/passes/simplify_cfg/defs/simplifyCfgDefsScript.sml | `simplify_cfg_fn`, `simplify_cfg_fn_ok` |
| Structural lemmas (proved) | venom/passes/simplify_cfg/proofs/simplifyCfgLabelPropsScript.sml | `simplify_cfg_fn_metadata` (name etc.), label-map facts |
| Well-formedness | venom/defs/venomWfScript.sml | `wf_ssa`, `fn_defs_reach_uses`, `fn_phis_cover_preds`, `fn_phi_operands_single_def` |
| Dispatcher | venom/defs/venomPassDispatcherScript.sml | what `fn_pass_step` runs for VP_SimplifyCFG |

## Notes

- A statement check (by reading, not built) found both provable, and
  found these facts unstated in the tree: "no PHI in `fn_insts` is kept
  by `simplify_cfg_fn`" (the closest template is the `[local]` raw-FMP
  chain in `simplifyCfgLabelPropsScript.sml`, `scfg_blocks_no_raw_*`; do
  not edit that file, put a PHI version in a new theory under
  `venom/passes/simplify_cfg/proofs/`); `wf_ssa fn /\ wf_function fn ==>
  fn_defs_reach_uses fn`; `entry_fn_no_return` excludes an `IntRet` from
  `run_context`; `ctx_eom_bounded` carried by the pass
  (`simplify_cfg_fn_metadata` gives the static layout unchanged).
- `MEM (l,v) (phi_pairs ops) ==> ?op. resolve_phi l ops = SOME op`
  exists only as `[local]` copies elsewhere; restate it.
