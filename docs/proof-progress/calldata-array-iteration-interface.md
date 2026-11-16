# Array iteration interface diagnostic (C1.9.7.3)

## Scope and evidence level

`calldataArrayIterationProbeTheory` is a bounded diagnostic, **not an exact
array decoder theorem**. It changes no supplier or frozen family header and
introduces no semantic predicate. Its ML schemas and applications are terms,
not assumptions, axioms, or proved propositions. In particular the fixed child
schema is conditional on exactly one coherent `ce/env/sf/ty/tv`; it is not
universally closed over all child types.

The final build is `holbuild(targets=["calldataArrayIterationProbeTheory"])`.
The diagnostic assertions require the instantiated accepted child's footprint
to be alpha-equal both to the raw return-frame input and to the second input
of scratch accumulation. The setup and observed-backedge application terms
also typecheck. These checks do **not** discharge their antecedents.

## Expanded child and loop instance

The fixed child schema retains the baseline execution, allocation, freshness,
source, and pointer clauses of `calldataExactInterfaceProbe` and adds accepted
value robustness and unchanged accounts/transient/logs/outcomes/requests/
pending-deletions/transaction-context/block-context/fmp/gas-readings.

The concrete child instance uses:

- compiler interval `ready` to `child_end`, the same ambient `limit`;
- input state `a` and source operand `FST (SND ops)`;
- destination operand `Var child_name` at `dst+32+j*type_memory_size tv`;
- source word `n2w (cd_member_ptr F a.vs_call_ctx.cc_calldata tv
  (cd_at F sb 32) (j*tv_abi_size tv))`.

The explicit loop-prefix quotation carries `j<count`, `count<=bound`, exact
source values for the first `j` elements, `LENGTH xs=j`, well-formed values,
robust old cells, counter lookup/value/cleanliness, root allocation and covers,
output containment/nonwrap, local interval ownership, frontier, unchanged
ambient freshness, and accumulated scratch witnesses. This is a typechecked
candidate invariant, not a proof that every iteration establishes it.

## Discharge/residual ledger

| Seam | Checked fact or application | Remaining obligation |
|---|---|---|
| Source header | `array_iteration_modular_header`: `cd_at F (w2n p) 32 = w2n (p+32w)`; normalized-member theorem permits reducing `(sb+32)` modulo the word modulus. | Join the lower operational setup with this modular address in the full iteration. |
| Wrapping source | `array_iteration_wrapping_header` proves that source `dimword(:256)-16` has data start 16 and fails the wrapper's `sb+32 < dimword` premise. | Do not add a nonwrap premise to the parent. This is a wrapper restriction, **not** a counterexample to any family theorem. |
| Setup execution | Specialized `calldataDynStep.calldata_element_setup_reentry` constructs `run_inst_seq` and computed operands without source nonwrap or global history. | Supply code shape, live old operands, counter value and ambient freshness at setup. |
| Setup pointer/origin | `decoderArraySetupPtr.calldata_array_element_setup_endpoint_ptr_origin_core` consumes that same successful sequence; has no global-history or source-header-nonwrap premise. | Counter pointer/cleanliness, destination slice bounds, code/cursor facts and lower frontier for its path. No independent runtime witness should be selected. |
| Global history | Raw wrapper explicitly requires `alloca_history fn s`; exact child schema has only local allocation-site ownership. `array_iteration_cursor_frontier` proves frontier is independent of the cursor. Definitions show history includes per-block allocation order and already-executed allocation sites. | No inference from frontier/local ownership to global history was proved. Bypass the raw convenience wrapper using the lower setup boundaries, rather than strengthen the parent. |
| Child call | Expanded fixed-child instance typechecks, retaining robust accepted value and world frame, common `H/u` before universal dead-set quantification. | Restrict outer ownership to child interval; show code/phi/live/bounds and transport same-limit freshness. The child contract remains a hypothesis, not a theorem. |
| Accepted return | Child footprint is alpha-equal to instantiated `calldata_array_raw_child_return_frame` input. Existing supplier supplies unchanged counter and physical prefix window. | Instantiate allocation-ID separation/output containment/scratch witnesses from the loop invariant and child result; these are explicit inputs, not automatically discharged by term matching. |
| Robust old prefix | `array_iteration_robust_prefix` is proved: translated return window plus shrinking dirty set preserves every old robust cell. Proof uses `val_footprint_le`, `mem_bytes_at_translated_window`, `calldata_member_robust_window_frame`. | For a full iteration, also transport through counter-write/backedge ghosts. Physical equality alone is insufficient. |
| Scratch union | Instantiated `calldata_footprint_accumulate` accepts exactly the child's footprint as its second frame and accumulates `old++sc` inside root footprint. | Supply first accumulated frame and slice containment; transport old scratch witnesses using existing `calldata_scratch_witness_transport`. No assumption that capacity bytes are all clean. |
| Backedge | Observed-header-step instance `st0=body_st`, `middle=ready`, `st1=child_end`, ABI stride `tv_abi_size tv` typechecks. Its conclusion has a physical prefix window. | Existing observed step does **not** expose `gas_origin_ptr_path`, robust values or ambient freshness; it cannot alone close the stronger exact schema. Need zero-event counter-write/backedge origin-pointer and dirty-set/robust-value transport. |
| Edge cases | `array_iteration_index_edges` proves vacuous prefix for `j=0`/empty list, `j+1=count` increment identity and `SUC j=count`, and absence of an iteration for `count=0`. | These are arithmetic/prefix checks only, not a zero-count execution certificate. |

## Consequence for the constructor plan

The full loop should remain risk-gated. The probe does not validate release of
C1.9.7.2 merely because raw-callsite and return-frame suppliers exist. The
smallest required interface work is (1) a modular, history-free setup join
reusing the two lower setup suppliers, and (2) a counter-write/backedge boundary
preserving the exact schema's same-limit freshness, world fields, robust
completed cells and zero-event origin-pointer path with common ghosts. Existing
interval restriction and scratch accumulation results should be reused.

No missing premise in an inherited admitted helper has been demonstrated:
these are insufficient convenience interfaces/remaining composition proofs,
not authority to alter a frozen target, strengthen a supplier, or report an
external-precondition blocker. No full remaining-count induction was attempted.
