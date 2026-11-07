# Canonical ASSIGN one-step boundary

Checked in `fnPlanLineageCanonicalAssignTheory`. This is not a proof or counterexample of `lineage_state_block_plan`.

Input: `inst = mk_inst 0 ASSIGN [Var a] [y]`, `a <> y`, empty spilled map, and literal stack `MAP Var (liveness_transfer [] inst nl)`. No width bound or output-freshness premise is needed. The preparation stack theorem does not require distinctness of `nl`.

Write `core = MAP Var (FILTER (\v. v <> y) nl)`. The complete `lineage_regular_prepare` stack is `core ++ [Var y]`. `canonical_assign_observe` then applies exactly the native nonhalting dead-output pop phase (stackPlanGen lines326--333); observation is before optimistic swap and release_dead_spills.

| Source a in nl | Output y in nl | Input stack | Observation stack |
| --- | --- | --- | --- |
| yes | yes | core | core ++ [Var y] |
| yes | no | core | core |
| no | yes | core ++ [Var a] | core ++ [Var y] |
| no | no | core ++ [Var a] | core |

All four combinations are allowed. A still-live source can occur at arbitrary depth: `do_dup_stack_exact` gives an appended copy even for the deep implementation, after which singleton reorder is identity. A last-use source already occupies the top. Consumption removes that copy and pushes y. Dead-output removal removes only the top y.

For nonempty `nl` with `y <> LAST nl`, its last element belongs to core and remains present at observation. `canonical_assign_observe_last` proves the requested candidate (with ALL_DISTINCT as requested, though the stronger stack equation does not need it). No query-hit, spill-selection, stack-height, or shadow-exclusion premise has been added.

Scope: this result validates only the stated canonical single ASSIGN family with empty initial spilled map. It does not establish preservation of canonical order (live y moves to the top), subsequent query safety, PHIs, loops, inherited queries, respills, or a native whole-function counterexample. Those require strategist classification; the frozen theorem and definitions remain unchanged.
