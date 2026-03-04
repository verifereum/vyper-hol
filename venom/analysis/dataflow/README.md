# Dataflow Framework

Generic lattice and worklist infrastructure for dataflow analyses. No project-specific dependencies in `defs/` — reusable for any analysis that fits the lattice/worklist pattern.

## Structure

```
defs/
  dfIterateDefsScript.sml  — df_iterate (round-robin WHILE-based fixpoint)
  latticeDefsScript.sml    — partial_order, bounded_measure, monotone, inflationary
                              Uses reflexive/transitive/antisymmetric from relationTheory.
                              Candidates for upstreaming to HOL4.
  worklistDefsScript.sml   — wl_step, wl_iterate, wl_deps_complete, is_fixpoint
proofs/
  dfIterateProofsScript.sml — df_iterate convergence proofs
  latticeProofsScript.sml   — monotone composition, Kleene fixpoint, measure monotonicity
  worklistProofsScript.sml  — convergence: termination, fixpoint, above-initial, invariant
dfIteratePropsScript.sml   — re-exports df_iterate proofs via ACCEPT_TAC
latticePropsScript.sml     — re-exports lattice proofs via ACCEPT_TAC
worklistPropsScript.sml    — re-exports worklist proofs via ACCEPT_TAC
```

## Design

Convergence theorems take an **invariant P** parameter:
- `∀lbl st. P st ⟹ leq st (process lbl st)` — inflationary under P
- `∀lbl st. P st ⟹ P (process lbl st)` — P preserved
- `P st0` — P holds initially

This supports analyses where inflationary only holds for well-formed states (e.g. liveness needs `lr_consistent`). For unconditional inflationary, instantiate `P = λ_. T`.

## Usage

To instantiate for a new analysis, prove:
1. Inflationary under your invariant P
2. P is preserved by processing
3. P holds for initial state
4. `bounded_measure` for your lattice ordering
5. `wl_deps_complete` for your dependency function
