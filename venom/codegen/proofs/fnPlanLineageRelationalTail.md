# Conditional ordinary relational consumer

`native_regular_conditional_shared_core_replay` is a checked non-JMP
consumer. It imports Setup in a separate leaf, avoiding both a cycle and a
second expansion of the native preparation pipeline. Its proof uses
`lineage_regular_prepare_decompose` once per branch and the existing
one-sided `optimistic_swap_plan_shielded_bottom_frame` on both prefixes.

The common base state includes all non-stack fields, including arbitrary
persistent spill maps and allocator state. Neither stack distinctness,
canonical order, empty spills, nor universal prefix exclusion is assumed.
The result supplies identical full regular code and a common final base
state, hence in particular equal final allocators. Cleanup height/promise
are not selected by this conditional instruction theorem.

## Exact premises still owed by native producers

1. Two actual preparation equations with the same preparation operations
   and a single common base `r`, extending it by the two residual prefixes.
2. Two actual conditional dead-output-pop equations with identical pop
   operations and common base `t`. The condition is exactly native:
   outputs nonempty and (nonhalting or more than one output). When skipped,
   the input equations use the identity pair, not a fabricated deletion.
3. At the actual enabled optimistic stage (outputs nonempty and some
   output next-live), either next-live is empty, the LAST query occurs in
   `t.ps_stack`, or it occurs in neither residual prefix. This is not
   asserted at block entry or at the preparation boundary. No obligation
   is imposed in the branch which skips optimistic swap.

The no-output branch directly returns release_dead_spills of `r`. The
no-live-output branch returns release_dead_spills of `t`. The remaining
branch performs the real optimistic swap and release. Thus no-output,
no-pop, no-swap, halting, and deep scratch-allocation behavior are retained
by the native decomposition and existing frame theorem.

This is not a proof of any native shielding premise, preparation/pop
confinement, PHI replay, successful JMP alignment, cleanup alignment, or
path propagation. In particular equal common spills are allowed, but do
not imply joint prefix exclusion when a shared occurrence is removed.
`native_regular_shared_core_replay` in Setup remains a distinct producer-
consumer with stronger global exclusion/coverage premises; it cannot be
replaced by importing this leaf without introducing a dependency cycle.
The new theorem does not duplicate that producer argument.
