# TASK: MakeSSA's first run places no degenerate PHI

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: venom/passes/make_ssa/proofs/makeSsaCurrentNonDegenerateScript.sml (project root: this directory)

## Theorem Statement (FROZEN)

The cheated theorem in `venom/passes/make_ssa/proofs/makeSsaCurrentNonDegenerateScript.sml`:

```sml
Theorem make_ssa_current_fn_phis_non_degenerate:
  EVERY (\inst. inst.inst_opcode <> PHI) (fn_insts fn) /\
  fn_defs_reach_uses fn /\ all_reachable fn /\ fn_inst_wf fn /\
  wf_function fn /\ first_block_no_preds fn /\ first_block_no_phi fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (fn',s') ==>
  fn_phis_non_degenerate fn'
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

`fn_phis_non_degenerate` and the `fn_*` premises are in `venom/defs/venomWfScript.sml`; `all_reachable` in `venom/defs/cfgWfScript.sml`; `first_block_no_preds` in `venom/compiler/unitShapeDefsScript.sml`; `first_block_no_phi` in `venom/compiler/o1PassContractScript.sml`. **Do not modify these definitions or `makeSsaCurrentDefsScript.sml`.**

## Completion Criteria

1. The build below passes with zero CHEAT warnings in `makeSsaCurrentNonDegenerateTheory`.
2. Helper lemmas go in `makeSsaCurrentNonDegenerateScript.sml` or in new theories under `venom/passes/make_ssa/proofs/`; each exists once in its most general form, and existing lemmas are reused rather than re-proved.
3. No change to existing theories.

**If the theorem is false as stated:** produce a HOL4 counterexample (EVAL on concrete values of `make_ssa_current_fn`), state the tightest sufficient fix, and do NOT weaken the statement.

## Build

```
holbuild --max-heap 8000 -j4 build makeSsaCurrentNonDegenerateTheory
```

Run from this directory (the one with `holproject.toml`).

## Background

The O1 pipeline runs `make_ssa_current_fn` twice per function. The second run's correctness needs `fn_phis_non_degenerate` of its input: every PHI reads two distinct values, neither its own output. The PHIs that input has are the ones the first run placed (later passes don't touch PHIs). This theorem is that fact for the first run, whose input has no PHI. With no PHI in the input the pass's PHI cleanup doesn't run, so every output PHI is a placed one: pruned, at the iterated dominance frontier of the variable's definitions, one `Label p; Var v` pair per predecessor, then renamed along the dominator tree.

`make_ssa_current_fn_wf_ssa` (`makeSsaCurrentWfSsaScript.sml`, proved) applies here, its PHI premises holding vacuously, and gives `ssa_form` and `def_dominates_uses` of the output.

## Domain Constraints

- Use holbuild only (no Holmake, no REPL sessions).
- No `cheat` in the result. No `TRY`/`ORELSE` around metis or other search. Never raise the tactic timeout.
- No `let` in theorem statements. Prefer existing lemmas to re-proving them.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| Pass definitions | `venom/passes/make_ssa/defs/makeSsaCurrentDefsScript.sml` | make_ssa_current_fn and its parts |
| Current-variant lemmas | `venom/passes/make_ssa/proofs/makeSsaCurrent*Script.sml` | placement, frontier queries, renaming traces, tree paths, availability, the wf_ssa proof |
| Dominators | `venom/analysis/dominators/` | compute_df, dom_frontier_correct |
| Well-formedness | `venom/defs/venomWfScript.sml`, `venom/defs/cfgWfScript.sml` | wf_ssa, fn_dominates, fn_reachable, is_fn_path |
