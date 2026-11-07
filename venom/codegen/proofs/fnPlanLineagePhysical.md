# Spill-permitting physical inventory validation (in progress)

Search found that `lineage_inventory` in fnPlanLineageInventory already
expresses the proposed exact inventory, for S = set (MAP Var live).
`physical_live` is therefore only an alias, not a duplicate definition.
`physical_live_explicit` proves equivalence to the exact strategist-specified
marker-prefix/MAP-Var/distinct/disjoint/union formulation. The variable-only
spill-key condition in lineage_inventory follows from the exact union.

Checked so far:
- `physical_live_init`: exact canonical marker-prefix initialization with
  distinct live list and empty spills.
- `physical_live_emit_dead_source`: actual last-use emit_one_input preserves
  physical inventory, whether the source is already on stack or restored
  from a persistent spill. No allocator constraints or empty-spill premise.

Remaining validation is NOT proved. Follow native singleton reorder, source
consumption, dead-output push/pop and release to obtain physical_live nl.
The first nontrivial conservation interface after the checked emitter is
singleton reorder preserving exact physical inventory under source presence
and absence of that source from spills. Existing do_restore and do_spill_at
lineage_inventory boundaries are available; no general exact-inventory
reorder theorem was found.

`reorder_plan_marker_core_inventory` is not immediately applicable: it takes
residual_budget_wf, while `residual_budget_wf_canonical` requires
plan_slots_bounded and spill_alloc_layout_wf in addition to the physical
conditions. The candidate intentionally has no allocator-layout assumptions.
Do not silently add those assumptions or treat lack of this convenience
interface as a refutation of physical preservation. This is a search finding,
not yet a checked preservation residual. The authorized next action is to
inspect/attempt the singleton physical conservation step or report its exact
residual, not redesign native reachability or start the frozen theorem.
