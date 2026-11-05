# TASK: MakeSSA's O1 step contract

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: venom/compiler/o1ContractMakeSsaStepScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem make_ssa_step_contract_at:
  k = 0 \/ k = 4 ==> o1_step_contract_at k rpolicy (CFP_Simple VP_MakeSSA)
```

`o1_step_contract_at_def`, `fn_pass_step_def`, `o1_fn_shape_def`,
`fresh_names_ok_def`, `label_map_sources_ok_def`, `o1_fn_row_def`,
`make_ssa_input_ok_def` (and the reduction `o1_step_contract_at_preserve`)
are in `venom/compiler/o1PassContractScript.sml`. `fn_shape_ok_def`,
`retpc_shape_ok_def`, `opaque_use_ok_def`, `inst_shape_ok_def`,
`label_positions_ok_def`, `call_checks_ok_def`, `copy_phi_var`, `gas_var_def`,
`retpc_var_def`, `reachable_fn_def` are in
`venom/compiler/unitShapeDefsScript.sml`. The pass is `make_ssa_current_fn`
in `venom/passes/make_ssa/defs/makeSsaCurrentDefsScript.sml`; the dispatcher
case is `execute_configured_fn_pass_make_ssa` in
`venom/defs/venomPassDispatcherScript.sml`.

MakeSSA runs at walk positions 0 and 4 only, which is why the statement
is limited to them.

Premises you get (from `o1_step_contract_at_def` and `o1_fn_row k fn`, for
k = 0 and k = 4):

- `make_ssa_input_ok fn` (all blocks reachable, definitions reach their
  uses, the PHI conditions);
- `no_raw_fmp_ops fn` (k = 0 only);
- `fmp_sig_no_param fn`, and `EVERY fmp_sig_no_param` over the observed
  context's functions;
- at k = 4 also: no ALLOCA, `fn_pseudos_prefix fn`, and no PARAM-family
  opcode outside the first block.

Scope: the row conclusion `o1_fn_row (SUC k) out.fpo_function` is proved by
hand separately as `make_ssa_step_rows` in a new theory
`venom/compiler/o1MakeSsaRowsScript.sml`. You may assume it (cite it by name;
if it doesn't exist yet when you get there, state it as a local `cheat`ed
lemma in your OWN new helper theory with exactly this statement and say so
at the end; it will be replaced):

```sml
Theorem make_ssa_step_rows:
  fn_pass_step rpolicy (CFP_Simple VP_MakeSSA) observed s fn out /\
  o1_ctx_shape observed.cu_context /\ ir_supply_inst_ok s /\
  EVERY fmp_sig_no_param observed.cu_context.ctx_functions /\
  (k = 0 \/ k = 4) /\ o1_fn_row k fn ==>
  o1_fn_row (SUC k) out.fpo_function
```

Your job is the other four conjuncts: `o1_fn_shape`, `fresh_names_ok`,
`label_map_sources_ok`, `ir_supply_inst_ok`.

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j4 build o1ContractMakeSsaStepTheory` passes with zero CHEAT
   warnings and zero failures.
2. `holbuild check o1ContractMakeSsaStepTheory:make_ssa_step_contract_at`
   reports no cheat, oracle or axiom.
3. The statement above is unchanged.
4. No change to any existing file other than
   `venom/compiler/o1ContractMakeSsaStepScript.sml`. New helper theories go
   in new files in `venom/compiler/` (next to the target). No new cheat
   anywhere, except the stated `make_ssa_step_rows` stand-in above.
5. No duplicate or near-duplicate lemmas: search before adding a helper.
   A proved lemma from the reference checkouts below may be ported into a
   new helper theory (adapted to this branch's definitions).

**If the theorem is false as stated:** produce a concrete counterexample
(an input function meeting the premises, with `EVAL` on
`make_ssa_current_fn`), say which conjunct fails and the tightest fix, and
stop. Do NOT weaken the statement.

## Build

```
holbuild -j4 build o1ContractMakeSsaStepTheory
```

## Background

The O1 pipeline proof of the Vyper compiler (Venom IR) runs each pass on
one function at a time. Every pass owes a structural "step contract": given
a function of a context with the O1 shape, its output still has the O1
function shape (`o1_fn_shape`: well-formedness, the unit shape facts
`fn_shape_ok`, first block without predecessors or PHIs, invoke and label
references, no DRET, DALLOCA outputs not gas/return-pc variables, the
entry/non-entry return clauses), its new labels and instruction ids come
from the supply, its label map is sound, the supply stays ok, and the
function row carries over (out of scope here, see above).

This task is that contract for MakeSSA (`VP_MakeSSA`, run twice in the
pipeline). The input function is not assumed to be in SSA form, but it
meets `make_ssa_input_ok`. Comments above the theorem in the
script give an informal argument for each part.

The same contract is proved for other passes; their proofs show how the
conjuncts are discharged: `venom/compiler/o1ContractSueStepScript.sml`
(SingleUseExpansion) and `venom/compiler/o1ContractCfgNormStepScript.sml`
(CFG normalisation).

## Domain Constraints

- Don't change any definition (executable pass, semantics, contract) or
  any existing theorem.
- holbuild only, default per-step tactic timeout (no override). No `TRY`
  or `ORELSE` around `metis_tac` or other search; select goals with `>~`,
  `>-`, `>|`.
- New theories: `Theory`/`Ancestors` headers, `Theorem ... Proof ... QED`.
  Don't name a theory with a `Lib` suffix.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| Target | `venom/compiler/o1ContractMakeSsaStepScript.sml` | the frozen theorem |
| Contract | `venom/compiler/o1PassContractScript.sml` | step contract, `o1_fn_shape`, `fn_pass_step`, `make_ssa_input_ok` |
| Shape defs | `venom/compiler/unitShapeDefsScript.sml` | `fn_shape_ok`, `retpc_shape_ok`, `copy_phi_var`, `reachable_fn`, lemmas about them |
| Templates | `venom/compiler/o1ContractSueStepScript.sml`, `venom/compiler/o1ContractCfgNormStepScript.sml` | the same contract for SUE and CFGNorm |
| Skeleton using it | `venom/compiler/o1ContractMakeSsaScript.sml` | how this theorem is consumed |
| MakeSSA defs | `venom/passes/make_ssa/defs/makeSsaCurrentDefsScript.sml` | `make_ssa_current_fn` and its parts |
| MakeSSA props | `venom/passes/make_ssa/proofs/makeSsaCurrentPropsScript.sml` | supply (`make_ssa_current_fn_supply_ok`, `_extends`), labels (`_labels`, `_structural`), invoke targets, `_no_raw_fmp_ops` |
| Other MakeSSA proofs | `venom/passes/make_ssa/proofs/` | `makeSsaCurrentInduct`, `makeSsaHelper`, ... incl. `make_ssa_current_fn_wf_ssa` (makeSsaCurrentWfSsa), `make_ssa_current_fn_input_ok` (makeSsaCurrentInputOk), `make_ssa_current_fn_phis_non_degenerate` (makeSsaCurrentNonDegenerate); `makeSsaCurrentSim` still has a cheat: don't rely on it |
| Dominators | `venom/analysis/dominators/defs/dominatorDefsScript.sml` and `venom/analysis/dominators/` | `dom_analyze`, `compute_df` (frontiers only at join points), idom, dominator props |
| CFG | `venom/analysis/cfg/` | `cfg_analyze`, preds/succs, reachability |
| Liveness | `venom/analysis/liveness/` | `liveness_analyze` |
| Supply | `venom/defs/irSupplyScript.sml` | `fresh_ir_var`, `fresh_inst_id`, `ir_supply_inst_ok`, covers |
| Well-formedness | `venom/defs/venomWfScript.sml` | `wf_function`, `bb_well_formed`, `fn_inst_wf` |
| Your earlier helpers (on this branch, built) | `venom/compiler/o1MakeSsa*Script.sml` | reusable: CFG preservation (`o1MakeSsaCfg`), frontier and PHI insertion (`o1MakeSsaFrontier`, `o1MakeSsaFrontierAncestry`), opcode/format preservation (`o1MakeSsaFormats`), reachability, rename visit traces and names (`o1MakeSsaVisit*`, `o1MakeSsaActualNames`, `o1MakeSsaClosure`, `o1MakeSsaTreeBoundary`), ... Read their headers before adding anything new. The finite probe theories were removed; the earlier dead-predecessor counterexample is excluded by `make_ssa_input_ok` |
| Reference: MakeSSA bisim machinery (read-only, older base) | `alan-ref/makessa3/venom/passes/make_ssa/proofs/` | ~600 proved units about `make_ssa_current_fn`'s rename stacks, dominance and inserted PHIs (e.g. `makeSsaCurrentDominanceBridge`, `makeSsaCurrentFrontier`, `makeSsaCurrentLastSite`, `makeSsaCurrentPhiLocality`, `makeSsaCurrentDefined`); proved under `make_ssa_input_ok`-style premises, which this task now has; `alan-ref/makessa3/TASK_makessa.md` explains them |
| Reference: SSA-form proof (read-only, older base) | `alan-ref/makessa-wf/venom/passes/make_ssa/proofs/makeSsaCurrentWfSsaScript.sml` | proved `make_ssa_current_fn_wf_ssa` |

The `alan-ref/` checkouts are not built and not on this branch: port what
you need into a new helper theory in `venom/compiler/`; don't import them.

## Notes

- With `all_reachable` from `make_ssa_input_ok`, every block is renamed and
  every idom/frontier entry is a real one.
- `make_ssa_current_fn` is the identity when `fn_entry_label fn = NONE`.
