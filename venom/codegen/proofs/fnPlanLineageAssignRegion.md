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
