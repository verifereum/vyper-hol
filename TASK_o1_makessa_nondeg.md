# TASK: MakeSSA leaves no degenerate PHI

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: venom/passes/make_ssa/proofs/makeSsaCurrentNonDegenerateScript.sml (project root: this directory)

## Theorem Statement (FROZEN)

The cheated theorem in `venom/passes/make_ssa/proofs/makeSsaCurrentNonDegenerateScript.sml`:

```sml
Theorem make_ssa_current_fn_phis_non_degenerate:
  make_ssa_input_ok fn /\ fn_inst_wf fn /\ wf_function fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (fn',s') ==>
  fn_phis_non_degenerate fn'
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

`fn_phis_non_degenerate`, `fn_inst_wf`, `wf_function` and `wf_ssa` are in `venom/defs/venomWfScript.sml`; `make_ssa_input_ok` and `first_block_no_phi` in `venom/compiler/o1PassContractScript.sml`; `first_block_no_preds` in `venom/compiler/unitShapeDefsScript.sml`; `make_ssa_current_fn` in `venom/passes/make_ssa/defs/makeSsaCurrentDefsScript.sml`. **Do not modify these definitions, `makeSsaCurrentDefsScript.sml`, or any existing theory**, including the helper theories listed below (they are shared copies; other work merges the same bytes).

## Completion Criteria

1. The build below passes with zero CHEAT warnings in `makeSsaCurrentNonDegenerateTheory`, and the frozen theorem's proof contains no `cheat`.
2. New helper lemmas go in `makeSsaCurrentNonDegenerateScript.sml` or in NEW theories under `venom/passes/make_ssa/proofs/` (name them `makeSsaCurrentNonDeg*`). Each lemma exists once in its most general form; reuse existing lemmas rather than re-proving them.
3. The only admitted (cheated) theorem the proof may cite is `makeSsaCurrentWfSsaTheory.make_ssa_current_fn_wf_ssa`. Cite no other cheated theorem, and add no new cheat anywhere.

**If the theorem is false as stated:** produce a HOL4 counterexample (EVAL on concrete values of `make_ssa_current_fn`), state the tightest sufficient fix, and do NOT weaken the statement.

## Build

```
holbuild -j4 build makeSsaCurrentNonDegenerateTheory
```

Run from this directory (the one with `holproject.toml`).

## Background

MakeSSA (`make_ssa_current_fn`) runs twice in the O1 pipeline: first on PHI-free input, then on the first run's output, which has PHIs. The second run's correctness needs `fn_phis_non_degenerate` of its input: every PHI with a single output reads two distinct values, neither its own output. This theorem gives it for any run satisfying `make_ssa_input_ok`.

Two cases, told apart by `had_phis = blocks_have_leading_phi fn.fn_blocks`:
- PHI-free input (`had_phis = F`): the cleanup `simplify_current_phis_if` does nothing, so every output PHI is one the pass placed (pruned by liveness, at the iterated dominance frontier of the variable's definitions, one `Label p; Var v` pair per predecessor) and then renamed along the dominator tree.
- PHI input (`had_phis = T`): the cleanup `simplify_current_phi_raw` turns every PHI whose non-self inputs are all equal into an ASSIGN (or a NOP when there are none); the PHIs it keeps have two different non-self inputs.

`make_ssa_input_ok fn` has `fn_phis_non_degenerate fn`, `fn_defs_reach_uses fn` and `all_reachable fn`; on PHI-free input its PHI clauses hold vacuously. `make_ssa_current_fn_wf_ssa` gives `wf_ssa fn'` (hence `ssa_form`).

## Domain Constraints

- Use holbuild only (no Holmake, no REPL sessions).
- No `cheat` in the result. No `TRY`/`ORELSE` around metis or other search; select goals with `>~`, `>-`, `>|`. Never raise the tactic timeout (2.5 s per step); a slow step is split, not tolerated.
- No `let` in theorem statements. Prefer existing lemmas to re-proving them.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| Pass definitions | `venom/passes/make_ssa/defs/makeSsaCurrentDefsScript.sml` | `make_ssa_current_fn`, placement (`add_phi_nodes_supply`, `insert_phis_for_var_supply`), renaming (`rename_current_blocks`), cleanup (`simplify_current_phis_if`, `simplify_current_phi_raw`) |
| Structural MakeSSA facts | `venom/passes/make_ssa/proofs/makeSsaCurrentPropsScript.sml` | labels, metadata, supply, instruction shape preserved by the pass |
| Proved MakeSSA machinery | `venom/passes/make_ssa/proofs/makeSsaCurrent{Placement,PlacementCut,Frontier,PhiLocality,Tree,TreePaths,TreeTrace,RenameTrace,EdgeTrace,FinalSlots,FinalBlock,TraceCertificate,Certificate,Allocation,Tokens,TokenGraph,GraphCut,LastSite,CutTokens,SingletonCut,DemandedCut,SourceCuts,PathBridge,DominanceBridge,Analysis,Demand,DemandBoundary,DemandDominance,Availability,SelectedLive,LiveTransport,Occurrence,DefSupport,CleanupShape,CleanupBoundary,SimDefs}Script.sml` | placement at the iterated frontier, frontier queries, dominator-tree traversal, renaming traces (which name each slot/operand receives), liveness demand, cleanup shape |
| Dominator/liveness helpers | `venom/passes/make_ssa/proofs/{dominatorQueryProofs,dominatorRankProofs,livenessDemandWitness}Script.sml` | dominator query and rank bounds, liveness use witnesses |
| Old full wf_ssa proof (read-only reference) | `alan-ref/old_makeSsaCurrentWfSsaScript.sml.txt` | the proof of `make_ssa_current_fn_wf_ssa` built on the machinery above; its internal lemmas are NOT available as theorems here (the theory on this branch holds only the admitted statement). If you need one, prove it in a new `makeSsaCurrentNonDeg*` theory. |
| Admitted wf_ssa | `venom/passes/make_ssa/proofs/makeSsaCurrentWfSsaScript.sml` | `make_ssa_current_fn_wf_ssa` (cite-able) |
| Dominators | `venom/analysis/dominators/` | `compute_df`, dominance frontier correctness, `dominatorAnalysisProps` |
| Liveness | `venom/analysis/liveness/` | liveness analysis and its proofs |
| Well-formedness | `venom/defs/venomWfScript.sml`, `venom/defs/cfgWfScript.sml` | `wf_ssa`, `ssa_form`, `bb_well_formed` (PHI prefix), `phi_well_formed`, `fn_dominates`, `fn_reachable`, `fn_defs_reach_uses` |
| Instructions | `venom/defs/venomInstScript.sml` | `phi_pairs` |

## Notes

Intuition for both cases is in the comment above the theorem in its script.
