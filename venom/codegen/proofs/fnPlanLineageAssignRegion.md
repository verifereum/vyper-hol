# Symbolic ASSIGN region interface (in progress)

This leaf encodes, but does not prove, the arbitrary-length safety candidate.

- `assign_region_live` computes backward ordered liveness over pairs (source,output).
- `assign_region_ready` requires different source/output, distinct outputs and no use of an output earlier or at its defining position.
- `assign_region_safe` retains actual forward planner states and checks each active LAST observation. It does not recanonicalize. The next-terminator flag is false throughout this straight-line query-active schedule.
- `assign_region_step` is exactly the SND of the actual nonhalting regular ASSIGN transition, with analysis contexts arbitrary.
- `assign_region_step_postprocess` is checked: successor = release_dead_spills of the observed state, after optimistic_swap_plan iff y is live. Thus observation is not the next entry state.
- `assign_region_canonical_head` discharges the initial observation from the literal canonical input, then leaves precisely `assign_region_safe ... rest ... (assign_region_step ... ps)`.

Remaining candidate: from ALL_DISTINCT exit, assign_region_ready schedule, initial stack MAP Var (assign_region_live schedule exit), and empty spills, derive assign_region_safe. No such universal theorem has been exported. An iterable physical relation is still required; literal canonical order is not established by the first-head lemma.

Before attempting that relation, inspect the dead-output branch: it skips optimistic swap entirely. `do_dup` has exact append stack behavior and `do_swap` uses bulk spill/restore for deep swaps; neither alone is the selective-spill obstruction. A last-use source passed to reorder_plan is the place where selective spilling may occur if it is no longer on top. Any invariant must handle runs of dead-output instructions without assuming future queries hit. No concrete fixture or word enumeration is authorized.

This document records an unfinished induction interface, not a positive region result or a counterexample to the frozen theorem.

## Physical-boundary attempt and exact residual (2026-11-07)

Tested `assign_region_physical nl ps`: distinct stack, exactly the members
of `MAP Var nl`, and empty spill map. This is weaker than literal order
and is initialized by `assign_region_physical_init`. It is a candidate,
not a preserved invariant. It deliberately does not reset native order.

The dead-output, last-use branch is now exposed by checked boundaries:
`assign_region_dead_prepare` and `assign_region_dead_step_stack`. If neither
source `a` nor output `y` belongs to next-live `nl`, and the source is not
spilled, the *full* successor stack is exactly

```
stack_pop 1 (SND (reorder_plan dfg [Var a] ps)).ps_stack
```

There is no optimistic swap in this branch. The output is pushed and popped;
release_dead_spills changes no stack entries. Thus this equation includes
the actual continuation rather than an imagined canonical successor.

Attempting preservation from `assign_region_physical (nl ++ [a]) ps`
leaves exactly: distinctness of the displayed stack, membership equality
with `MAP Var nl`, and emptiness of the native successor's spill map.
The checked FAIL_TAC residual is tool output
`TO_lineage_after_fix-20261106T221649Z_m12735_t001`; the temporary unfinished
theorem has been removed.

This boundary loses the relevant order information. Singleton reorder of
a last-use source may call reduce_depth_plan when its depth exceeds 16;
all other operands are outside its forbidden singleton. They can be live
members of `nl`, so membership/distinctness alone cannot exclude their
selective spilling. release_dead_spills retains live spills. Consequently
this candidate cannot justify the empty-spills preservation claim or the
subsequent observation guarantee by a set-valued argument. No claim that
such an adverse permutation is natively reachable from canonical backward
liveness has been established: initialization alone is not reachability.
The actual native reachable-order restriction remains the missing fact.

This is an induction-interface obstruction, not a checked refutation of
the region candidate, and still less a counterexample to the frozen task.
No width/word fixtures or arbitrary-core witnesses were constructed. Return
to ancestor review before strengthening this candidate or expanding opcodes.
