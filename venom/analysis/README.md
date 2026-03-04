# Venom Static Analyses

Static analysis infrastructure and implementations for the Venom IR.

## Subdirectories

- **`cfg/`** — Control flow graph construction and properties (predecessors, successors, DFS ordering)
- **`dataflow/`** — Generic dataflow framework: lattice predicates, worklist iteration with convergence guarantees. Reusable by any dataflow analysis.
- **`fcg/`** — Function call graph analysis
- **`liveness/`** — Liveness analysis: which variables are live at each program point. Instantiates the dataflow framework.

## Top-level files

- `dfgAnalysisScript.sml` — Data flow graph (DFG) analysis for PHI/ASSIGN chains
- `dfgAnalysisCorrectnessScript.sml` — DFG analysis correctness proofs
