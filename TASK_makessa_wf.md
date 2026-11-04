# TASK: MakeSSA (supply variant) produces well-formed SSA

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Location: venom/passes/make_ssa/proofs/makeSsaCurrentWfSsaScript.sml (project root: this directory)

## Theorem Statement (FROZEN)

The cheated theorem in `venom/passes/make_ssa/proofs/makeSsaCurrentWfSsaScript.sml`:

```sml
Theorem make_ssa_current_fn_wf_ssa:
  fn_defs_reach_uses fn /\ fn_phi_operands_single_def fn /\
  fn_phis_cover_preds fn /\
  (!bb inst. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
     inst.inst_opcode = PHI ==>
     ALL_DISTINCT (MAP FST (phi_pairs inst.inst_operands)) /\
     !l v. MEM (l,v) (phi_pairs inst.inst_operands) ==>
       fn_cfg_edge fn l bb.bb_label) /\
  fn_phi_outputs_single_def fn /\ fn_phis_non_degenerate fn /\
  all_reachable fn /\ fn_inst_wf fn /\ wf_function fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (fn',s') ==>
  wf_ssa fn'
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

`wf_ssa` (= `ssa_form` /\ `def_dominates_uses`), `def_available_at`, `phi_edge_uses_wf` and the `fn_*` premises are in `venom/defs/venomWfScript.sml`; `all_reachable` in `venom/defs/cfgWfScript.sml`; `first_block_no_preds` in `venom/compiler/unitShapeDefsScript.sml`; `first_block_no_phi` in `venom/compiler/o1PassContractScript.sml`. **Do not modify these definitions or `makeSsaCurrentDefsScript.sml`.**

## Completion Criteria

1. The build below passes with zero CHEAT warnings in `makeSsaCurrentWfSsaTheory`.
2. Helper lemmas go in `makeSsaCurrentWfSsaScript.sml` or in new theories under `venom/passes/make_ssa/proofs/`; each exists once in its most general form, and existing lemmas are reused rather than re-proved.
3. No change to existing theories.

**If the theorem is false as stated:** produce a HOL4 counterexample (EVAL on concrete values of `make_ssa_current_fn`), state the tightest sufficient fix, and do NOT weaken the statement.

## Build

```
holbuild --max-heap 8000 -j4 build makeSsaCurrentWfSsaTheory
```

Run from this directory (the one with `holproject.toml`).

## Background

The O1 pipeline runs `make_ssa_current_fn` twice per function: first on PHI-free input, then on input that already has the PHIs the first run built, plus non-SSA redefinitions of fresh variables made by later lowering passes. The same statement covers both runs. The passes after the second run need its output in SSA form with every use dominated by its definition.

The pass:
- computes the CFG, dominators and Python-faithful liveness of `fn`;
- inserts pruned PHIs at iterated dominance frontiers, with one `Label p; Var v` pair per predecessor;
- renames along the dominator tree. The first definition of a variable keeps its spelling; later ones get fresh names from the IR supply. Existing PHI operands are renamed per predecessor edge.
- only when the input had PHIs, cleans up degenerate PHIs into ASSIGN or NOP.

The premises are those under which the same run is proved (separately) a function bisimulation of its input, plus one: each input PHI names every label at most once, and only predecessors. That one is needed because the pass never drops a PHI pair, so a pair naming a non-predecessor survives into the output and breaks `phi_edge_uses_wf`. The comments in `venom/compiler/o1ContractMakeSsaScript.sml` say why each one is needed. The legacy, name-based variant has `make_ssa_fn_ssa_form` (`makeSsaSsaFormScript.sml`), an output-distinctness proof that may be adaptable.

## Domain Constraints

- Use holbuild only (no Holmake, no REPL sessions).
- No `cheat` in the result. No `TRY`/`ORELSE` around metis or other search. Never raise the tactic timeout.
- No `let` in theorem statements. Prefer existing lemmas to re-proving them.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| Pass definitions | `venom/passes/make_ssa/defs/makeSsaCurrentDefsScript.sml` | make_ssa_current_fn and its parts |
| Current-variant lemmas | `venom/passes/make_ssa/proofs/makeSsaCurrent*Script.sml` | supply freshness/coverage, labels, structure, dom-tree induction, placement, renaming traces, cleanup, availability, dominance bridges |
| Legacy SSA-form proof | `venom/passes/make_ssa/proofs/makeSsaSsaFormScript.sml` | ALL_DISTINCT outputs for make_ssa_fn |
| Analyses | `venom/analysis/cfg/`, `venom/analysis/dominators/`, `venom/analysis/liveness/` | cfg_analyze, dom_analyze, liveness_analyze and their correctness facts |
| Supply | `venom/defs/irSupplyScript.sml`, `venom/defs/venomFnScheduleRunnerScript.sml` | fresh_ir_var, ir_supply_covers_fn |
| Well-formedness | `venom/defs/venomWfScript.sml`, `venom/defs/cfgWfScript.sml` | wf_ssa, def_dominates_uses, fn_dominates, fn_reachable |

## Notes

- The `makeSsaCurrent*` theories in this worktree come from a parallel run proving the bisimulation; build on their lemmas freely, but do not edit them.
