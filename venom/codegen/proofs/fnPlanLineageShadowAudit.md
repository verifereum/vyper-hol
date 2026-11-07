# Native optimistic shadow provenance audit

Scope: C3.native_shadow_provenance, following accepted E0389. This is a
proof-design audit, not a proved invariant or a counterexample certificate.
The frozen theorem and definitions are unchanged.

## Exact call and required boundary

`fnPlanLineageSetupScript.sml:1452` (`lineage_regular_prepare_decompose`)
rewrites a non-JMP regular call as preparation, optional dead-output pop,
optional optimistic swap, and spill release. The optimistic call is made
only when `FILTER (\out. MEM out nl) inst.inst_outputs <> []`.
For an *active* call additionally `~term`, `nl <> []`, and
`~operand_equiv dfg (Var (LAST inst.inst_outputs)) (Var (LAST nl))` hold.
The FILTER guard implies some output is live; it does NOT imply that
`LAST nl` is an output, nor that it is the last output.

Put `x = Var (LAST nl)` and let `s` be the common state immediately before
this call, with concrete compared stacks `p ++ s.ps_stack` and
`q ++ s.ps_stack`. The new checked theorem
`optimistic_swap_plan_missing_suffix_code` says, when `s.ps_stack <> []`
and `~MEM x s.ps_stack`, equality of the p-call's code with the s-call's
code is equivalent to `~MEM x p`. The analogous condition holds for q.
This boundary does not classify two arbitrary prefix-hit calls against
each other: they might coincidentally emit equal code. It does rule out
using the common-state frame interface without exclusion.

Required native obligation: derive that exclusion from actual lineage/DFS
origins, readiness, and the actual phase equations, not from an assumed
replay property. A spilled-only x does not discharge it.

## Producers actually available

* `successful_join_edges_native_cells` (JoinEntry:29) assumes readiness,
  two successful predecessor block calls, a genuine join and nonempty PHIs.
  Its conclusion gives predecessor-specific prefixes and native cell
  suffixes, not any restriction on names in the prefixes.
* `generate_block_plan_join_edge_suffix` (Edge:87) also applies to joins
  without PHIs. `analyzed_join_edge_spilled_empty` (Edge:129) gives empty
  spills on successful analyzed join edges. Empty spills do not rule out
  stack duplicates.
* `lineage_dfs_join_phi_common_suffix_actual` (Lineage:664) additionally
  uses successful whole-function generation, native lineage and DFS states,
  nonentry reachable join and nonempty PHIs. It gives actual PHI runs with
  common code, common allocator and common suffix covering every post-PHI
  demanded variable. It does not give prefix exclusion. Its non-actual
  variant explicitly needs allocator agreement; this is not free on
  arbitrary state pairs.
* `analyzed_native_slot_state_replay` (PhiSchedule:317) preserves the
  supplied prefixes literally through the PHI run and provides common
  suffix live coverage. The selected-slot extinction machinery used there
  is not whole-stack exact-name extinction in residual prefixes.
* `ready_reachable_region_induction` (ReturnCut:401) requires `P entry`,
  `P` at every reachable join, and preservation from pred to lbl whenever
  `cfg_preds_of ... lbl = [pred]`. It concludes `P` on reachable labels;
  it supplies no physical preservation or state equality by itself.
* Frozen `lineage_state` step (Lineage:115) requires replay of the
  *predecessor* block's DFS code and copies its resulting stack/spills into
  the successor's DFS bookkeeping. This is not an exclusion premise for
  the successor. DFS sibling restoration similarly restores stack/spills
  but is not a name-disjointness theorem.

## Preservation ledger for a possible shadow x

1. **Already in join prefix.** Not excluded by the join producers above.
   Immediately after PHIs a demanded x is in the common suffix, so this
   duplicate is harmless for the suffix-hit frame. First unsupported
   strengthening at the root would be demanding all live names absent
   from prefixes; the actual root theorem does not assert this.
2. **Suffix becomes spilled.** `reduce_depth_plan_def` (Ops:152) can select
   a non-target candidate when an operand lies deeper than 16, and calls
   `do_spill_at`. That operation swaps the selected slot to TOS, pops one
   occurrence, and adds its name to the spill map (Ops:22-39). It does not
   delete all other occurrences of that name. Thus an old prefix copy is
   not erased merely because a suffix copy was spilled. The earliest
   unsupported *transition* after the checked post-PHI coverage boundary
   is preservation of suffix-only live coverage/exclusion through this
   spill branch during regular preparation. Candidate selection constrains
   current targets, not every next-live name. More exactly,
   `select_spill_candidate_def` restricts offsets to at most
   `MIN 16 (MIN (target_dist - 1) (LENGTH stack - 1))`, at least
   `target_len`, with a variable item not in forbidden targets. Thus the
   scenario additionally needs a long enough common part and an eligible
   shallow, unprotected occurrence; not every suffix spill is possible.
   No checked native theorem
   currently rules out this combination of origins and candidate choice.
   This is a symbolic operation possibility, not evidence of native
   reachability of all its premises.
3. **Consumption.** `lineage_regular_prepare_live_coverage` and
   `lineage_regular_preoptimistic_live_coverage` (Setup:1394,1434) retain
   demanded variables on stack OR in spills, assuming bounded operands and
   incoming demand coverage. These are exactly the validated guarantees;
   neither proves a live occurrence remains in the suffix. Restoration
   in `emit_one_input` happens for the current operands, not all of nl.
4. **PHI rename.** `generate_phi_plan_def` (Gen:129) pokes one selected
   slot, or duplicates it and pokes TOS. The checked native PHI schedule
   handles suffix classes and liveness; it leaves residual prefixes
   untouched. It cannot be promoted to global exact-name extinction.
5. **Dead-output deletion.** The pop requests are output names not in nl.
   Since x is in nl, x itself is not requested. `dead_output_pop_live_coverage`
   suffices for stack-or-spill retention, not prefix extinction. A fresh
   output is pushed into the common part by preparation, but native
   output-vs-prefix absence (especially across loop re-entry) is a separate
   obligation, not a consequence of syntactic distinctness of outputs.
6. **New names after the join.** Swaps/pops/spills cannot create a new
   variable name; `do_spill_at_stack_support` and
   `reduce_depth_plan_stack_support` (Inventory:5896,5912) are only subset
   statements. Output push, PHI poke and restoration can introduce stack
   occurrences. A native future-definition/old-prefix exclusion argument
   would be needed; subset support alone cannot provide that argument.

## Candidate and review result

A candidate *to investigate*, not assume, is: at each instruction boundary
with common stack K, common spill map M, and actual residual prefixes p,q,
for every next-demanded variable v, if `Var v` occurs in p or q then it
occurs in K. Combine this with stack-or-spill demand coverage and agreement
of allocator/spill observations, plus actual decomposition equations.
This allows harmless duplicates while K retains a copy; it is weaker than
whole-stack uniqueness. At the post-PHI boundary the demanded part follows
from common-suffix coverage. The reduce-depth spill transition above has
no established preservation proof for this candidate. For newly demanded
outputs and region transitions the necessary provenance premises are also
not yet supplied. Empty common stacks need separate treatment; E0389's
nonempty premise must not be dropped.

No justified inductive native invariant has emerged from the checked
interfaces. No symbolic scenario here proves the frozen theorem false.
Next strategy choice must address native spill-candidate/duplicate
provenance or use a different compared-state representation with proved
agreement; another stack-or-spill corollary cannot close this gap.
