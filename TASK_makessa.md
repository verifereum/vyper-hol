# TASK: MakeSSA (supply variant): function bisimulation and frame simulation

## Meta
Status: planned (third run; earlier runs refuted the statements without fn_phis_cover_preds/first_block_no_phi, and then with duplicate PHI outputs in one block)
Priority: P1
Created: 2026-11-02
Location: venom/compiler/o1ContractMakeSsaScript.sml (project root: this directory)

## Theorem Statement (FROZEN)

The two cheated theorems in `venom/compiler/o1ContractMakeSsaScript.sml`:

```sml
Theorem make_ssa_current_fn_fn_bisim:
  fn_defs_reach_uses fn /\ fn_phi_operands_single_def fn /\
  fn_phis_cover_preds fn /\
  fn_phi_outputs_single_def fn /\ fn_phis_non_degenerate fn /\
  all_reachable fn /\ fn_inst_wf fn /\ wf_function fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (fn',s') ==>
  fn_bisim fn fn'

Theorem make_ssa_current_fn_frame_sim:
  ctx_bisim C C' /\
  fn_defs_reach_uses fn /\ fn_phi_operands_single_def fn /\
  fn_phis_cover_preds fn /\
  fn_phi_outputs_single_def fn /\ fn_phis_non_degenerate fn /\
  all_reachable fn /\ fn_inst_wf fn /\ wf_function fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (fn',s') ==>
  frame_sim L C C' fn fn'
```

`fn_bisim`, `ctx_bisim`, `frame_sim` and their helpers are defined in `venom/compiler/o1PassLiftScript.sml`; its theorems are proved. `def_on_all_paths`, `fn_defs_reach_uses`, `fn_phi_operands_single_def`, `fn_phis_cover_preds`, `fn_phi_outputs_single_def` and `fn_phis_non_degenerate` are in `venom/defs/venomWfScript.sml`; `all_reachable` in `venom/defs/cfgWfScript.sml`; `first_block_no_preds` in `venom/compiler/unitShapeDefsScript.sml`; `first_block_no_phi` in `venom/compiler/o1PassContractScript.sml`.

**Do not modify these statements, these definitions, `makeSsaCurrentDefsScript.sml`, or anything in `o1PassLiftScript.sml`.** Prove them as-is, or produce a counterexample.

## Completion Criteria

1. The build below passes with zero CHEAT warnings in `o1ContractMakeSsaTheory` (cheats inherited from `o1PassLiftTheory` are expected and fine).
2. Helper lemmas go in new theories under `venom/passes/make_ssa/proofs/` (e.g. `makeSsaCurrentSimScript.sml` for the simulation, and new analysis-correctness facts next to the analysis they are about, in a new theory) or in `o1ContractMakeSsaScript.sml`; each exists once in its most general form.
3. No change to existing theories other than `o1ContractMakeSsaScript.sml`.

**If a theorem is false as stated:** produce a HOL4 counterexample (EVAL on concrete values of `make_ssa_current_fn` and, if needed, `run_blocks`), state the tightest sufficient fix, and do NOT weaken the statement.

## Build

```
holbuild --max-heap 8000 -j4 build o1ContractMakeSsaTheory
```

Run from this directory (the one with `holproject.toml`).

## Background

The O1 pipeline runs `make_ssa_current_fn` twice per function: first on PHI-free input, then (after LowerDload, ConcretizeMemLoc and FmpLowering) on input that already has the PHIs the first run built plus non-SSA redefinitions of fresh variables. The same statements cover both runs.

The pass computes the CFG, dominators and Python-faithful liveness of `fn`; inserts pruned PHIs (where the variable is live after the block's leading PHIs) at iterated dominance frontiers, with one `Label p; Var v` pair per predecessor; renames along the dominator tree (the first definition of a variable keeps its spelling, later ones get fresh names from the IR supply; existing PHI operands are renamed per predecessor edge); and, only when the input had PHIs, cleans up degenerate PHIs (all non-self inputs equal: ASSIGN, placed after the block's remaining PHIs; no non-self input: NOP; otherwise unchanged). Instruction ids are reassigned within each cleaned prefix.

These theorems are the per-function facts the pass contract needs: terminating runs correspond in both directions (`fn_bisim`), and every state the output's frame reaches corresponds to one the input's frame reaches with the same alloca frame and memory ranges (`frame_sim`).

Why each premise (each was checked necessary by an EVAL counterexample on the real pass):
- `fn_defs_reach_uses` (definite assignment): without it a PHI operand along a predecessor the run takes can be the never-written original spelling, and `eval_phis` errors where the input runs.
- `all_reachable`: the renaming walks only the dominator tree from the entry; with every block reachable every block is renamed (the legacy proof's `valid_dom_tree` asks the same).
- `fn_phis_cover_preds` and `first_block_no_phi`: a PHI with no operand for an edge the run takes errors in the input, while the cleanup can collapse it to NOP or ASSIGN and the output runs (an earlier run refuted the statements without them: an entry block `PHI [] -> x; STOP`).
- `fn_phi_outputs_single_def`: two PHIs in one block writing the same variable (parallel PHI semantics keeps the first value; renaming makes later uses read the second) refute the statements, and so does a PHI output redefined in another block (run 0 re-places a PHI for it at its own block; the self-edge strip collapses that PHI to an ASSIGN of an operand undefined on the entry edge). With it, a re-placed PHI for an existing PHI's output can only land in that PHI's own block and always collapses to `ASSIGN [Var v'] [v]` among the ordinary instructions.
- `fn_phis_non_degenerate`: an existing degenerate PHI in a loop header (`v = PHI [E,a; D,a]` at D) and the re-placed PHI for `v` both collapse to ASSIGNs in top-to-bottom order, so the copy of the renamed output runs before that name is defined. With two distinct non-self operands (which renaming keeps distinct and non-self under `fn_phi_operands_single_def` and `fn_phi_outputs_single_def`), every existing PHI stays a PHI through cleanup and defines its new name before the collapsed copy reads it.
- `fn_phi_operands_single_def`: the Python-faithful liveness (`input_vars_from`) drops a variable that is both a PHI operand and live past the PHI from other predecessors' live-out; for a single-definition variable that loss cannot change PHI placement.

The legacy, name-based MakeSSA (`make_ssa_fn`, `makeSsaProof`/`makeSsaSim`/`ssaRenamedSim`/`ssaPipeline`) has a same-fuel proof for PHI-free input under analysis-validity premises (`valid_dom_tree`, `valid_cfg_maps`, `valid_liveness*`, `live_in_scope`); its renaming-simulation machinery may be adaptable, and its analysis-validity premises have to be discharged for the current analyses here.

## Domain Constraints

- Use holbuild only (no Holmake, no REPL sessions).
- No `cheat` in the result. No `TRY`/`ORELSE` around metis or other search. Never raise the tactic timeout.
- No `let` in theorem statements. Prefer existing lemmas to re-proving them.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| Pass definitions | `venom/passes/make_ssa/defs/makeSsaCurrentDefsScript.sml` | make_ssa_current_fn and its parts |
| Current-variant lemmas | `venom/passes/make_ssa/proofs/makeSsaCurrentPropsScript.sml`, `makeSsaCurrentInductScript.sml` | supply freshness/coverage, labels, metadata, structure, dom-tree induction |
| Legacy proof | `venom/passes/make_ssa/proofs/` (makeSsaProof, makeSsaSim, makeSsaHelper, makeSsaSsaForm, ssaRenamedSim, ssaSimDefs, ssaPipeline, ssaPipelineProps, ssaOracle*, ssaFrame) | name-based variant |
| Analyses | `venom/analysis/cfg/`, `venom/analysis/dominators/`, `venom/analysis/liveness/` (defs and proofs, incl. livenessSoundProofs, livenessLocalProofs) | cfg_analyze, dom_analyze, liveness_analyze and their correctness facts |
| Lift | `venom/compiler/o1PassLiftScript.sml` | fn_bisim, ctx_bisim, frame_reach, mem_corr, call_corr, frame_sim |
| Supply | `venom/defs/irSupplyScript.sml`, `venom/defs/venomFnScheduleRunnerScript.sml` | fresh_ir_var, fresh_inst_id, ir_supply_covers_fn |
| Well-formedness | `venom/defs/venomWfScript.sml`, `venom/defs/cfgWfScript.sml` | the premises above, fn_reachable, is_fn_path, fn_dominates, fn_inst_wf, wf_function |
| Definedness from dominance | `venom/passes/sccp/proofs/sccpCorrectnessProofsScript.sml` (strict_dom_vars_defined_*) | existing runtime-definedness argument |
| Semantics | `venom/defs/venomExecSemanticsScript.sml` | run_defs, eval_phis, eval_one_phi, resolve_phi; `venom/defs/stateFrameScript.sml`: execution_frame |
| Exec props | `venom/props/venomExecPropsScript.sml`, `venom/simulation/crossBlockSimPropsScript.sml` | fuel monotonicity, determinism |
| Memory ranges | `venom/compiler/unitMemInvScript.sml` | inst_mem_ranges |
| Reachability | `venom/codegen/proofs/contextRawReachableScript.sml` | enters_block, active_inst |

## Notes

- See the SML comments in `o1ContractMakeSsaScript.sml`.
- This is a large proof; plan intermediate lemmas (analysis validity of the current analyses, a renaming simulation relation, the PHI-input renaming and cleanup) as separate theories.
