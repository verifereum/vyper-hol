# Direct-execution coupling readiness (.38)

This is an interface audit, not a proof of one-round simulation. The frozen
function theorem has not been edited. `loadElimCaptureInvariantTheory` checks
only the empty-history and fixed-history lookup-transport probes.

## Capture representation and phases

`phi_action` has join/load labels, load/phi IDs, output and PHI operands, but
**no key field**. `le_latest_captures m ctx cfg result actions h t` indexes
read obligations by each successful `compute_phi_action m cfg result key lbl
inst = SOME pa` witness for a member action. For each latest PHI occurrence
at that action's join, the incoming source key read must be defined and equal
to the target generated-register lookup. No all-alternatives currentness is
asserted. Quantifying all computation witnesses avoids selecting an arbitrary
key from an existential origin certificate.

This predicate belongs to the **post-PHI/body** phase. On an incoming edge,
the source history must not yet contain the new PhiOcc while the target
PHIs remain unexecuted. Control agreement and target index shift are separate
clauses, not fields of the capture predicate. Initial empty history imposes
no generated-variable requirements.

## Readiness matrix

All ordinary branches also require reached source occurrence, wf/SSA,
configured context, empty BP, alias matching, fixpoint, initial invariants,
and frozen step/PHI preservation where stated by the reached consumers.
These are not discharged by the local simulation lemmas.

| Branch | Checked interface | Remaining premises / intended supplier |
|---|---|---|
| Initial entry | `le_latest_captures_empty`, `le_entry_phis_empty`, `le_occ_prefix_actual_phis_frame` | Reflexive padded agreement/control initially; initial occurrence construction, entry lookup, source PHI success and predecessor distinctness must be connected to run_blocks. Entry has no collected actions. |
| Ordinary unchanged step | `le_padded_noncall_step`, `load_elim_inst_unchanged` / `load_elim_inst_changed` | Non-INVOKE/non-MEMTOP, operand Var lookup agreement, aligned control. Freshness/source membership supplies operand agreement. `step_inst_base` to `step_inst` and shifted index bookkeeping remain integration work. |
| Singleton load | `le_reached_singleton_load_replacement` | Source OK step, inst_wf, reached singleton lookup, padded equivalence. Frozen invariant propagation supplies DFG; no target replacement-evaluation oracle needed. |
| Captured multivalue load | `le_reached_captured_load_replacement`, `le_reached_collected_action_latest_join` | Current compute witness/key, SOME ops with length >1, actual action lookup, latest-join split, captured read and target generated lookup. Capture invariant supplies last two **after** action identity and provenance are reconciled. |
| Redundant store | `le_reached_store_replacement` | Actual nonempty store-test lookup/EVERY condition and successful source step; source reached invariants supplied as above. Exact transform branch classification must feed it. |
| Jump / PHI entry | `le_occ_prefix_actual_phis_frame`, `le_occ_prefix_all_entries_phis_success`, `le_occ_prefix_phi_selected_source_capture`, `le_actual_prepend_generated_lookup` | Incoming prev_bb and labels agreement; source-domain/padded agreement; predecessor distinctness; source occurrence and successful source batch. Generated refresh must be instantiated for each validated compute witness, then transported through actual original/rest PHIs. Existing dynamic collected-action capture exports only an existential origin key; it is not by itself the universal-key capture invariant. |
| Call | `le_padded_invoke_step` | `le_padded_control V`, INVOKE, decoded argument evaluation agreement, no-MEMTOP in all context functions. Same-program callee proof is already internal to this interface. Caller generated-register framing across returned continuation still needs connection to write exclusion and bind outputs. |
| Terminal result | `le_padded_noncall_step`, `le_padded_invoke_step` | Lifted Halt/Revert branches give padded equivalence directly; source Error discharges error alternative. Converting final padded relation to the frozen le_exec_equiv is separate outer composition work. |
| Fetch/index transitions | `le_actual_prepend_get_instruction`, `le_actual_prepend_phi_length`, `le_step_nonterm_rebase_OK`, `le_step_term_rebase_OK`, `le_body_increment_shift` | Body source index >= phi_prefix_length, get_instruction success, known inserted PHI count. Nonterminal OK continuations carry shift; terminator OK returns index zero. These do not alone handle terminal INVOKE results by overwriting indices. |

## Actual action-selection audit

* `phi_action_lookup_member` proves lookup success implies a member action
  with matching load ID and output. It does not identify its originating
  instruction occurrence.
* `collect_phi_actions_member` inverts membership to an indexed source load,
  its static read key/current-point lattice lookup and successful compute.
* `compute_phi_action_origin` supplies load ID and load label and fresh output.
* `le_reached_collected_action_latest_join` needs `pa_load_lbl = s_current_bb`;
  membership plus matching ID alone does not immediately supply this premise.
* The consumer needs the member's indexed load to be the reached instruction
  and its static block/index to be the reached point. No inspected theorem
  directly packages this identification. It needs the wf instruction-ID
  uniqueness and reached static-position interfaces, rather than a claim that
  arbitrary matching IDs imply matching keys.
* The converse, that a successful compute at a current eligible load is
  collected, is visible in `collect_phi_actions_def` but no checked public
  converse was found. It is distinct from membership inversion. If actual
  `phi_action_lookup` is NONE the multivalue load is unchanged, so completeness
  is not automatically necessary for simulation of that branch.

No proof of either missing selection direction was attempted in this audit.

## Exact transition obligations still to establish

Write `Cap(h,t)` for the fully parameterized `le_latest_captures` above.

1. **Source ordinary extension + target frame.** From Cap(h,t) and
   `!pa. MEM pa actions ==> lookup_var pa_phi_out t' = lookup_var pa_phi_out t`,
   derive `Cap(h ++ [StepOcc b n fuel x y],t')`. StepOcc cannot change which
   PhiOcc is latest. The fixed-history lookup probe covers only the second
   part. `le_collected_transformed_output_fresh` gives syntactic output
   exclusion for reached original instructions; successful target semantics
   must turn that into lookup framing, including INVOKE continuations.

2. **PHI refresh.** For `h' = h ++ [PhiOcc bb u p]`, establish Cap(h',q).
   For actions at bb's label, prove for every compute witness
   `?w. le_key_read space key u = SOME w /\ lookup_var pa_phi_out q = SOME w`.
   For other actions, preserve their old target lookups from t to q.
   `le_occ_prefix_phi_selected_source_capture` handles a specified compute
   witness given actual whole-batch success, incoming source-domain agreement,
   prev_bb agreement, predecessor distinctness, output distinctness, and
   action membership. `le_collected_other_join_phi_fresh` and
   `le_actual_prepend_generated_lookup` expose framing boundaries, but their
   application to the actual transformed PHI list remains to be checked.
   Initial entry must use entry action exclusion instead of assuming a
   noninitial predecessor exists.

3. **Body consumer discharge.** Derive actual action lookup witness's compute
   origin at the reached instruction/key; get latest split; specialize Cap
   to obtain the exact captured word required by the captured consumer.
   None of these facts follows from padded equivalence on generated names.

4. **Execution induction.** Generalize reached history and entry/body/edge
   phase across run_defs; append successful source occurrences; propagate
   frozen invariants; apply local consumers and restore control at edges.
   No coupling induction is begun here, and no successful target suffix is
   assumed as an invariant premise.
