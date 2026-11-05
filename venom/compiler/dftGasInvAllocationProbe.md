# Allocation scheduling diagnostic

Checked by `dftGasInvAllocationProbeTheory`; this is not a counterexample to
`dft_ev_lowered_inv` and establishes no general semantic exchange theorem.

## Decision table

All schedules below are checked equations for the actual `dft_block []`;
`dft_eda` and `entry_instructions` are evaluated, not replaced by
`build_full_eda`. Source IDs are consecutive starting at 0.

| Probe | Source opcodes | Scheduled IDs | Diagnostic |
|---|---|---|---|
| `inv_alloc_probe` | ALLOCA, ADD, STOP | 0,1,2 | No crossing in this example |
| `inv_alloc_after_probe` | ADD, ALLOCA, STOP | 0,1,2 | No crossing in this example |
| `inv_two_alloc_probe` | ALLOCA, ALLOCA, STOP | 0,1,2 | No crossing in this example |
| `inv_alloc_use_probe` | ALLOCA, ADD, MSTORE(a), STOP | 1,0,2,3 | Allocation/pure crossing |
| `inv_alloc_effect_probe` | ALLOCA, MSTORE(0), MSTORE(a), STOP | 1,0,2,3 | Allocation/effect crossing |
| `inv_two_alloc_use_probe` | ALLOCA(a), ALLOCA(b), MSTORE(a), STOP | 1,0,2,3 | Allocation/allocation crossing |

For each crossing the theory proves source `id_before ... 0 1` and target
`id_before ... 1 0`. Opcode lists and the ALLOCA barrier classification are
checked, as are all source ID lists. The dependent consumer is important:
the three smallest examples do not support a general barrier-exclusion claim.

## Consumer envelope

`inv_alloc_probe_family_wf` checks `EVERY inst_wf` and distinct instruction IDs
for every row. For the allocation/pure row, the concrete wrapper
`inv_alloc_probe_fn = mk_raw_function "probe" [inv_alloc_use_probe]` additionally
has checked `wf_function`, `wf_ssa`, and block membership. Its actual `dft_fn`
output is checked to have IDs `[[1;0;2;3]]`, so this crossing is not an artifact
of supplying an unattainable arbitrary order to `dft_block`.

For the other five rows, full SSA/function wrappers and actual `dft_fn` outputs
are **not checked**. Their results are specifically `dft_block []` results;
no claim of actual consumer-order attainability is made for them. There is no
checked `o1_ctx_shape`/reachable execution envelope or lowered-memory failure
for any row. No optional INVOKE probe was needed for this allocation diagnosis.

## Required boundary and planning consequence

The proposed generic inference from inversion to nonbarrier status is false,
even in the checked well-formed SSA actual-function allocation/pure example.
Canonical `build_full_eda` incomparability cannot discharge the actual scheduler
consumer. A conditional canonical helper would leave the same missing producer.

A replacement exchange argument must account for allocation state:

* Allocation/pure: starting from an actual successful ordered trace, produce
  success in the exchanged order, preserve the fixed oracle interpretation,
  and relate the observation operands as well as the allocation state.
* Allocation/effect: additionally relate memory effects and allocation effects;
  the schedule equation alone does not validate their semantic independence.
* Allocation/allocation: analyze allocation identities/results. Equality of each
  SSA pointer across reordered executions cannot simply be assumed; the two
  allocations can cross in the concrete block computation.

If equality-based exchange fails, a more observational invariant (possibly
allocation-bound rather than pointer-equality based) needs strategist design.
None is implemented or asserted here. Existing crossing totality proves success
of an inserted predecessor under readiness/nonstaticness; it does not prove
this exchange or source-prefix reconstruction. The parent simulation and
forwarding obligations remain unproved.
