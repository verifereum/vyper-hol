# Residual predecessor trace and operand agreement

`dftGasInvResidualTraceTheory` checks a bounded producer, not the full DFT simulation.

## Interface and provenance

`inv_ev_trace` records a finite instruction-list execution with actual successful oracle steps at fixed arbitrary fuel and the same index increment as the oracle next rule. It intentionally does not fetch instructions from a block. The existing `inv_ev_prefix` records block-indexed execution and cannot describe an arbitrary residual list without an exchange/correspondence proof; the two predicates have distinct roles.

`inv_remaining_trace_extension` constructs such a trace for an arbitrary finite residual predecessor list. It derives head readiness from the accepted SSA invariant at each intermediate state, manufactures success using the crossing classification, and preserves the remaining invariant using actual successful-step deletion. Nonstaticness is propagated by the accepted oracle call-context frame. No successful runs, operand agreement, or source reachability are added as hypotheses.

The observation operand values are preserved, not merely their definedness. For variables this uses disjoint defs/uses in the no-must-order hypothesis and successful non-output-variable preservation; the GAS update is handled explicitly. Labels use successful-step label preservation. Literals are state independent. These facts are composed through induction on the predecessor list.

Both INVOKE and CODECOPY predecessors are excluded by checked crossing tables for the memory-observation opcodes. Thus the general extension theorem has no separate CODECOPY-exclusion hypothesis. A common arbitrary fuel is legal here because no predecessor can be INVOKE; there is no callee return-reflection premise.

`inv_entry_trace_extension` is the connected entry consumer. It takes an entry-label-identified incoming state, actual successful PHIs, and the actual oracle pseudo prefix. It derives the initial residual invariant using the accepted pseudo-prefix/fold bridge and entry initialization. It then constructs an arbitrary-length trace and preserves the observation operands. It does not assume the initial remaining invariant. Structural pseudo partition, label bounds, well-formedness, nonstatic incoming state, and syntactic crossing constraints remain explicit inputs.

## What this unlocks and what it does not

The availability/totality gap in completion of a finite residual predecessor list now has an actual execution witness and stable observation operands. This supports the planned observation-specific trace completion.

It is not yet an actual source block prefix: previously deleted instructions, target order and flips have not been exchanged into original order. Source-prefix extraction/value agreement between reordered executions remains unproved. Also outstanding are production of arbitrary block-entry dominator facts, initial entry-state/structural premises from the full oracle semantics, finite returning-callee reflection, and concrete revert-forwarding preservation. The frozen lowered-memory theorem remains unproved.
