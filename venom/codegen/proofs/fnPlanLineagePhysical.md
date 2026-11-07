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

## Bounded singleton inspection (2026-11-07)

A temporary symbolic theorem (removed after inspection) unfolded the exact
singleton reorder, under physical_live live ps, an actual unfixed source hit
`stack_get_unfixed_depth (Var a) 0 1 ps.ps_stack = SOME d`, and
`FLOOKUP ps.ps_spilled (Var a) = NONE`. The verified simplification prefix
reduced the restoration branch to no-op. The first nontrivial intermediate
state is exactly

```
SND (if d > 16 then
       reduce_depth_plan (LENGTH ps.ps_stack) [Var a] (Var a) 0 1 ps
     else ([],ps))
```

The needed primitive interface is exact lineage_inventory preservation by
this reduction, including marker-prefix shape, distinct variable core,
stack/spill disjointness and equality of the union. Existing
`reduce_depth_plan_inventory_mono` requires residual_budget_wf;
`reduce_depth_plan_live_reserve` proves only lower multiplicity bounds;
`reduce_depth_plan_stack_support` proves only support inclusion. None
supplies this exact structural invariant from physical_live alone.
`do_spill_at_lineage_inventory` is the relevant one-step boundary, but it
requires a stack_get_depth equality for the chosen variable; the selector
returns a distance/peek and variable-ness instead. Connecting these requires
uniqueness of the variable in the marker core, then induction over the
actual reduction fuel. This interface has not been proved here.

After reduction, the placement branch still needs exact marker-core
preservation through the two stack_poke operations (equivalent-operand
branch) or do_swap dist' followed by do_swap 0. `do_swap_core` supplies the
latter once the hit is shown to lie in the variable core. No allocator
premise was added. This is a missing primitive interface / bounded proof
residual, NOT evidence that physical_live preservation or the frozen theorem
is false. No new admitted theorem was retained.

Evidence: tool output TO_lineage_after_fix-20261106T221649Z_m12801_t001.

## Exact primitive boundaries now checked

`fnPlanLineagePhysicalOps` now proves `reduce_depth_plan_lineage_inventory`
for arbitrary fuel and all target parameters, with lineage_inventory as its
only premise. The selected-variable peek-to-lookup inverse is proved once;
its selector corollary explicitly requires a nonempty stack. This premise
comes from the actual unfixed-depth hit in a mutating reduction branch.
Do not remove it: selector [] may inspect HD [], an unspecified operand.

`reorder_singleton_lineage_inventory` now proves exact inventory conservation
for the actual singleton reorder, including restoration, selective spilling,
early-stop/missing-hit cases, and both placement branches. The poke branch
uses `stack_poke_top_exchange` to identify an ordinary swap using the actual
source peek, never an assumption that operand_equiv means equality.
`do_swap_lineage_inventory` preserves the exact marker-prefix distinct core
and spill domain. Physical exports the alias corollary
`physical_live_reorder_singleton` and imports PhysicalOps.

These results discharge the primitive residual recorded above. They do NOT
prove singleton target-reaching or the full dead-last-use ASSIGN transition.
Consumption and native dead-output/release integration remain to be checked.
No external theorem copies, allocator assumptions, or admissions were added.
Evidence: TO_lineage_after_fix-20261106T221649Z_m12861_t001.

## Full bounded native dead-last-use transition checked (2026-11-07)

The earlier residual is now discharged:
- `reorder_singleton_source_top` derives actual top placement from an unfixed
  source hit, using `reduce_depth_plan_unfixed_hit` and actual swap results.
- `physical_live_consume_dead_source` combines placement, exact singleton
  conservation, length-floor, inverse variable-peek lookup and the existing
  exact popmany boundary. It removes precisely the source from inventory.
- `native_dead_assign_state` exposes the complete native dead-output ASSIGN:
  its push/pop cancels exactly, leaving release of the consumed emitted state.
- `physical_live_release_dead_spills` preserves exact live inventory.
- `physical_live_native_dead_assign` proves the full actual transition from
  `physical_live (a::nl) ps`, `~MEM a nl`, `~MEM y nl` to `physical_live nl`
  for `assign_region_step ... a y nl term ps`. This is slightly stronger than
  the requested probe: no `a<>y` premise is necessary when both names are dead.

All persistent live spills are allowed, and allocator fields are unconstrained.
No scratch admissions or external theorem copies were introduced. The proof
uses the actual emission, reorder, consumption, dead-output and release states;
it does not canonicalize intermediate stacks. This proves this bounded native
transition only, not global reachability, ASSIGN-region shielding, join
provenance, or the frozen theorem.
Evidence: TO_lineage_after_fix-20261106T221649Z_m12922_t001.
