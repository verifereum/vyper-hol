# Inverse temporal realizability search ledger

Scope: C3.temporal_realizability. No frozen theorem/definition edits.

## Bounds and current cursor

PLAN limits: regular ASSIGN/ADD words of length <=4, cores of 18--20 names,
<=256 fully evaluated local candidates, <=2 successful-local native embedding
attempts. So far **one** fully evaluated local candidate (one ASSIGN, core19),
**one** native embedding attempt started. No enumerator has yet been added.
Do not count the reversed-layout diagnostic as another native candidate.
No old selective_fn/shadow_fn fixture is mutated.

## Checked local candidate (fnPlanLineageInverseProbe)

- ASSIGN a -> y, exit = y,b0,...,b15,t,x.
- Literal liveness_transfer gives entry = b0,...,b15,t,x,a.
- Core = a,b0,...,b15,x,t; residual prefix = x.
- a is at depth18, target window1. Actual reduce_depth_plan emits
  SWAP1,SPILL0,SWAP1,SPILL32. First selected cell is sole common x;
  second is b15. Old top t stays depth0, protected by window1; it is NOT
  the second spilled cell. This is checked in inverse_native_reduction_calls.
- Full lineage_regular_prepare has identical code on core and prefix::core,
  with identical resulting records except the preserved prefix. Common x
  remains absent and spilled at the preoptimistic phase.
- Output y is live, LAST exit is x, and optimistic_swap_plan emits no code
  on common state but nonempty code with residual prefix x. Each fact is
  EVAL-certified; this is a local obstruction, NOT a native counterexample.

## First native embedding attempt

inverse_fn is a ready marker-free diamond (inverse_fn_markers checked): entry defines the 19 names, left/right JMP to join. Join begins
with the local ASSIGN; suffix uses x,t,b15,...,b0,y, then STOP.

Checked readiness and actual analyzed lists:
- live_vars_at analyze join 0 = local entry list.
- live_vars_at analyze join 1 = local exit list.
- left JMP join targets = MAP Var local entry list.

First violated embedding constraint: join targets have a at depth0,
whereas the inverse local core requires a at depth18. x remains on the
common stack after preparation from that target layout. join_target_ops
uses MAP of input_vars_from, NOT REVERSE. The separate reversed-entry
probe is just another local diagnostic, not a native join model.

Still to do: complete native actual origin and whole-function SOME checks
for this attempted embedding if needed to classify it; implement the bounded
inverse word enumerator/evaluator (or request review of the explicit local
positive plus first native mismatch before expanding). At most one further
successful-local native embedding is allowed. Neither bounded negatives nor
arbitrary-core discrepancy discharges/refutes lineage_state_block_plan.

Verification: holbuild target fnPlanLineageInverseProbeTheory passed.
