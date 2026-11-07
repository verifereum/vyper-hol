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

## Ordered observation schedule audit (C3.observation_schedule)

This section supersedes the *proposed continuous invariant*, not the checked
facts above. E0405 gives the exact local spill-shadow criterion; E0408's one
native adaptation failed to realize its bad case. Neither implies preservation.
No new fixture, global invariant, event datatype, or theorem is introduced here.

### Actual analyzer: exact within a block, set-only across edges

The ordered interface already EXISTS; no copied/generalized list lemma is
needed to establish its availability. Exact exported signature, written without
its source's local `let` binders:

```
wf_function fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
lookup_block lbl fn.fn_blocks = SOME bb /\
SUC i <= LENGTH bb.bb_instructions ==>
live_vars_at (liveness_analyze fn) lbl i =
  liveness_transfer fn.fn_blocks (EL i bb.bb_instructions)
    (live_vars_at (liveness_analyze fn) lbl (SUC i))
```

This is `livenessAnalysisProps.live_vars_at_transfer` (52-65), transported
from `livenessProofs.live_vars_at_transfer` (49-61), ultimately proved by
`livenessLocalProofs.liveness_recompute_transfer` (47-69). Equality is literal
list equality, not permutation, set equality, or equality to a separate order
state. The well-formedness, reachable/preorder membership, lookup, and index
bounds must be supplied by native callers; it is not an arbitrary-state rule.

Why set-based convergence does NOT destroy this equation:

* `dfAnalyzeDefs.df_fold_backward_def` (109-117) folds the entire instruction
  list backwards, stores exit at length, and stores each transferred list at
  its index. `df_fold_block_def` starts from FEMPTY at index zero.
* `livenessDefs.liveness_block_def` (152-163) gathers successor inputs, does
  that full fold, and replaces the block slice by `FUNION inst_map st.ds_inst`.
* `livenessInvariantProofs.lv_coherent_def` (14-24) says every processed
  block slice is exactly a full backward fold of ITS STORED EXIT. Its
  `lv_coherent_transfer` (120-138) gives literal adjacent-list equality.
* `livenessLocalProofs.liveness_recompute_coherent` (10-15) transports this
  invariant; `liveness_recompute_processed` (18-37) ensures reachable seeded
  blocks were processed. `liveness_recompute_transfer` uses both.
* In contrast `livenessConvergenceProofs.liveness_recompute_convergence`
  (85-94) gives only `same_vars stored_exit (liveness_out ... final_state)`.
  `same_vars_set` identifies that with equality of sets. The driver has NO
  final refold (`livenessDefs`:193). Therefore do NOT replace the stored exit
  by the current successor gather as a LIST, nor transport LAST across an
  edge using convergence. `liveness_recompute_edge_subset` is set inclusion.

`liveness_transfer_def` is exactly `live_update inst_defs ordered_inst_uses`;
`live_update_def` filters defined names from the old list, preserving survivor
order, then folds uses left-to-right, appending a use only when unseen.
`ordered_inst_uses_def` uses `python_stack_operands`, not raw inst_operands.
The existing `MEM_FOLDL_append_unseen`, `live_update_ALL_DISTINCT`,
`MEM_ordered_inst_uses` and `live_update_mem` are membership/distinctness
interfaces, not LAST/rank theorems. A later barrier proof can use the literal
adjacent equation above, but still needs a proved LAST classification and a
link between relative liveness order and physical spill position. Neither is
established by this audit. Generic LAST algebra alone would not supply that
physical link, so no detached list-algebra helper is added.

### Operation ledger: discharge is not automatic at every query

* `emit_one_input_def` (Gen:23-48) checks FLOOKUP and calls do_restore for a
  spilled variable BEFORE stack_get_depth, independently of its live/dead
  status. `Inventory.do_restore_exact` (2009) appends the variable in the
  common stack, removes its spill entry, and frees the shared slot. This
  supplies a genuine local restoration barrier; subsequent consumption or
  re-spilling must still be handled. `emit_one_repeated_var_restored` (2037)
  is an existing exact instance, not a universal native scheduling proof.
* `emit_input_plan_cons` threads all operand restorations before regular
  reorder; pending-use liveness includes later operands. JMP separately
  invokes `restore_spilled_plan` on all join targets before reorder.
* `reorder_one_def` queries stack_get_unfixed_depth FIRST and restores only
  if missing there. Thus it is NOT by itself restore-before-query: an old
  prefix hit can suppress that restoration. For regular operands the earlier
  emit phase is relevant, but restoration can be followed by another spill
  during reorder. `reduce_depth_plan` queries the target, spills a forbidden-
  target-excluded candidate, and repeats. Selection and do_spill_at themselves
  inspect positions. Every such query needs its existing frame premises.
* `optimistic_swap_plan_def` (Gen:108-123) directly queries Var(LAST nl),
  with no spill lookup or restoration. The active guards additionally require
  a nonterminator next instruction, outputs and nl nonempty, and output-last
  not operand_equiv to nl-last. The dispatcher also requires some live
  output, NOT that LAST nl is an output. `Setup.optimistic_swap_plan_suffix_hit_frame`
  (1296) works with a suffix hit; `optimistic_swap_plan_missing_suffix_code`
  (2048) exhibits the unresolved prefix-observation case.
* Dead-output pop, release_dead_spills and output push lie between regular
  reorder and the next instruction. Popmany queries output names; it must
  not be treated as restoration. An output push can discharge the name's
  common absence, but old-prefix/future-definition provenance is separate.
  PHI uses stack_get_phi_depth/poke without the emit barrier. OFFSET and
  PHI must retain their own validated phase boundaries. The existing native
  PHI schedule is a root boundary, not a temporal preservation proof.

### Precise candidate obligation and scope of this result

Use the actual `native_inst_prefix` calls (EntryProduction:218-229), not a
new abstract trace: its step supplies DROP k xs = inst::rest and the exact
SOME dispatcher call with next-live at k+n+1 (or stored exit len), and the
actual next-terminator flag. Split each such call using the existing regular
preparation/preoptimistic decomposition. Start at the checked actual native
post-PHI common suffix and shared spill-map/allocator boundary, retaining the
actual residual prefixes and both successful native origins.

Candidate temporal obligation, NOT proved: for x = Var(LAST nl) at any active
unprotected optimistic call in this native run, if an earlier selective spill
removed the last common x while x occurred in a retained residual prefix,
then between the LAST such loss and this query there must be a shared
restoration of x or a common production of x, surviving to this query. Equivalently,
there can be no interval from an unmatched last-common-copy spill to the first
unprotected query for x. The active-call guards above, actual analyzed nl,
ready function, successful function plan, native DFS/lineage origins, and the
post-PHI common boundary are essential contextual premises, not an assumed
per-instruction shadow safety condition. Other unprotected query sites in the
ledger must be discharged separately; this optimistic obligation alone does
not establish full replay or cover region transitions.

The exact intra-block ordered recurrence supports INVESTIGATING this route;
set-only cross-edge convergence does not refute it, but does limit any rank
transport across blocks. No existing fact here connects liveness rank to the
first shallow candidate selected during native reorder. That physical/temporal
producer, including inherited (not newly appended use) LAST entries and
re-spills in the same instruction, is the remaining obligation for strategy
review. Do not infer it from E0408, membership convergence, shared spills,
or the local mandatory operand restoration equation.
