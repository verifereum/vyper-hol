# Current supply MakeSSA: readiness interface audit

Scope: C1.8.3.28.segment.readiness_audit. This report is not a proved global invariant. Paths below are relative to venom/passes/make_ssa/proofs/ unless stated otherwise. No protected definition is changed.

## Actual consumer, not a hypothetical global theorem

TemporalWritesScript = makeSsaCurrentTemporalWritesScript.sml:74-90 exports:

```
current_singleton_copy_agreement:
 (selected = n \/ selected = dst) /\
 ALOOKUP snapshot n = SOME origin /\ ALOOKUP snapshot dst = SOME origin /\
 ALOOKUP m n = SOME origin ==>
 ALOOKUP snapshot selected = SOME origin /\
 current_origin_copy m n dst m = SOME ((dst,origin)::m) /\
 ALOOKUP ((dst,origin)::m) dst = SOME origin
```

The direct variant requires only snapshot n and current m n equal the same SOME origin. The self-selected variant needs the old destination binding to have that same origin. These hypotheses are NOT established by allocation uniqueness or definedness. `current_intervening_write_changes_origin` (95-103) explicitly rules out replacing equality with mere availability.

makeSsaCurrentPrefixRuntimeScript.sml:7-27 `current_selected_prefix_ready` additionally consumes, for every retained prefix PHI, a selected slot for actual predecessor p, a concrete incoming SOME value and Q agreement; `current_copy_schedule Q known copies` is an explicit premise. It produces successful parallel PHIs followed by successful sequential copies, not those premises. Its `current_prefix_ready_token_values` (47-55) consumes a demanded-name available-or-untouched disjunction. There is no existing universal complete-block readiness establishment theorem in these interfaces. The proposed Entry/Ord signatures in makeSsaCurrentAlignmentProbeScript.sml:76-163 are comments, not HOL constants or proved statements.

## Exact available interfaces

1. Actual occurrences: makeSsaCurrentPhaseShapeScript.sml:195ff `current_certificate_phase_blocks` starts from current_structural_certificate, wf_function, fn_inst_wf, all_reachable, entry_block, supply coverage/inst_ok and an actual old block split into phis ++ tail. It exposes actual replay/cleaned block lookups and leading-PHI/suffix lengths. At 94-104 `current_cleanup_if_occurrence` says an occurrence k in pre is at rank `if enabled then current_cleanup_occurrence_rank pre k else k`, with equality modulo `current_inst_no_id`. Retained rank (113-118) lies in the retained parallel batch; copy rank (126-132) follows that batch. These are positions, not execution facts; IDs cannot represent repeat visits.

2. Origin transport: makeSsaCurrentJointRuntimeScript.sml:9-21 defines
```
current_origin_realizes V M st <=>
 !n. lookup_var n st = case ALOOKUP M n of NONE => NONE | SOME o => V o
current_joint_rel V M N rs D st st' <=>
 execution_frame st = execution_frame st' /\
 st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
 current_origin_realizes V M st /\ current_origin_realizes V N st' /\
 (!v. MEM v D ==> ALOOKUP M v = ALOOKUP N (latest_current_name rs v))
```
At 53-71 snapshot-copy and sequential-copy laws require a SOME origin with V origin = SOME value. At 144-152 paired fresh write requires realization of both maps and effective absence of the new origin in both; it extends V and prepends synchronized bindings. It does NOT preserve the last demanded-lookup conjunct automatically. `current_ordinary_demand (i::rest) exit = operand_vars i.inst_operands ++ current_before_outputs i.inst_outputs (current_ordinary_demand rest exit)` (74-79) supplies backwards local demand inclusion only.

3. Placement completeness: makeSsaCurrentPlacementCutScript.sml:85-98 `current_actual_insertion_prefix` relates actual add_phi_nodes_supply output to per-block pre ++ old instructions and the exact equivalence
```
current_actual_inserted fn v old.bb_label <=>
 ?i. MEM i pre /\ MEM v i.inst_outputs
```
`current_actual_inserted` is existential compute_defs roots and current_pruned_reach (7-15). Seed (132-139) needs actual definition occurrence, frontier edge and selected placement liveness. Step (120-126) closes an inserted site along another live frontier edge. This is a static fixed-point characterization, not a theorem saying each dynamically needed name was executed.

4. Definite assignment/path: makeSsaCurrentAvailabilityScript.sml:7-18 `current_available fn v l i` quantifies over every nonempty entry-to-l path and requires a definition in an earlier block occurrence or at j<i in the current block. `current_available_cross` (46-51) transports successor-entry availability to predecessor exit; `current_available_skip` (20-25) crosses a non-defining instruction backwards. makeSsaCurrentDemandDominanceScript.sml:7-13 exports `current_live_post_phi_available` from wf_function, fn_inst_wf, fn_defs_reach_uses, actual lookup, post-leading-PHI cut bounds and live_vars_at membership. At 74-83 its single-definition specialization gives a dominating definition block and a local earlier-index witness. It does not give the *last dynamic* definition at a repeated site or target store equality.

5. Liveness exception: makeSsaCurrentLiveTransportScript.sml:61-71 `current_live_cut_to_pred_exit` needs both no defining PHI in destination prefix and no occurrence of v among ANY PHI operand variables there. At 137-148 current_live_route_edge includes these restrictions, so arbitrary executed CFG segments cannot simply be declared live routes. makeSsaCurrentDemandBoundaryScript.sml:107-111 states exactly:
```
MEM v (input_vars_from src instrs live) ==>
 (?phi. MEM phi (collect_phis instrs) /\ MEM (src,v) (phi_pairs phi.inst_operands)) \/
 (MEM v live /\ !phi. MEM phi (collect_phis instrs) ==>
   ~MEM v (MAP SND (phi_pairs phi.inst_operands)))
```
This is one-way provenance, NOT a converse preserving all live variables on every edge. makeSsaCurrentDemandedCutScript.sml:10-14 derives the <=1 definition bound from fn_phi_operands_single_def and any original PHI operand occurrence. At 78-89 `current_actual_demanded_cut_tokens` proves equality of predecessor block static token and successor inherited static token only when no actual inserted PHI, current_phi_cut_clear, selected live membership, actual CFG edge, and both dominator token chains hold. Its exceptional branch (32-45) handles PHI operands through single-definition dominance rather than pretending liveness transport holds. Static token equality still needs interpretation by the actual chronological stores.

## Candidate induction invariant (proposal, not a theorem)

Index a finite actual execution prefix by visit ordinal and source instruction/output positions; retain source/target incoming snapshots at block entry and the actual certificate-derived target phase/rank. Maintain:

- [task assumptions] Exactly the frozen hypotheses, including PHI operand/output uniqueness, nondegeneracy, coverage and entry shape; no new global readiness hypothesis.
- [existing static theorem] One supplied actual structural certificate; actual source/target occurrences and prefix/suffix alignment from PhaseShape. Repeated execution uses a NEW visit ordinal even on a self-edge.
- [unproved induction obligation] Both concrete prefixes are actual semantic executions with corresponding effects; ghost maps are obtained only from those executions: genuine source writes produce fresh origins, corresponding target writes share them; merges/copies transport origins, not create source writes. The paired_writes/paired_runtime planned boundaries handle ordinary local production, not this entire clause.
- [existing local relation, unproved preservation] current_origin_realizes for both effective maps with shared V; equal execution frame and labels. Fresh origin prefixes absent from both maps. Define origins for entry bindings separately (visit 0); arbitrary initial stores cannot be silently replaced with empty stores.
- [unproved principal invariant] At each demanded source cut v, the certificate-selected target name has the SAME effective dynamic origin as source v. For every retained-PHI selected operand additionally maintain predecessor-edge interpretation against the fixed incoming snapshots. For a singleton collapsed inserted PHI, maintain the direct/self-selected origin agreement required by current_singleton_copy_agreement, derived from earlier execution plus placement, not assumed at entry.
- [unproved history support] A name denoting an ancestor static token realizes the latest relevant execution of that definition occurrence on this path until an actual intervening write to that name. A target-name history alone or a source history alone cannot justify cross-map equality. Demands determine which histories must be compared; no blanket no-write interval is valid.

## Adversarial phase checks and missing steps

**Initial entry.** first_block_no_phi and first_block_no_preds exclude a selected predecessor PHI edge. Initialization must use fn_bisim's actual initialized call state (params, labels, data, etc.), not only init_venom_state. Need an initialization theorem assigning compatible entry origins and showing demanded pre-definition reads cannot arise under fn_defs_reach_uses. An empty-store example is not this theorem.

**Ordinary instruction.** Backwards demand identifies operands and surviving demands. Actual paired event values are needed before shared fresh origins can be allocated; independent footprints cannot synchronize values. After production, prove surviving target names were not overwritten and each demanded output's latest_current_name selects the last correct output occurrence (duplicates allowed). Existing frame/name agreement and realization algebra supply only parts of this step. Recursive INVOKE needs a separate call rule, not base-dispatch success.

**Inserted PHI.** Read its selected predecessor name in the FIXED target incoming snapshot, then write the merged output in the parallel post-state. Need runtime definedness and equal source-v origin on the actual edge. Static placement seed/closure does not prove these; a CFG segment argument must show either the representative executed definition survives or a live separating frontier forced a merge. Its liveness propagation must branch on the existing-PHI operand exception above.

**Retained existing PHI.** All inputs use FIXED incoming snapshots, including when another PHI in the same batch writes an input spelling. The source PHI writes a new genuine dynamic origin, shared with its retained renamed counterpart, not with whichever source definition its input happened to read. Source output uniqueness and retained target output separation permit the complete batch, but per-slot correspondence alone does not prove post-batch agreement. Task nondegeneracy protects retention, not runtime definedness.

**Collapsed copy after retained PHIs.** Read CURRENT target map after the ENTIRE retained batch and preceding sequential copies, not the incoming snapshot. A reinserted original-PHI output copies the newly produced retained-PHI origin. An ordinary singleton uses the direct case or, on self-selection, needs snapshot destination = snapshot nonself = current nonself. Both names being defined is insufficient; a later overwrite can change origin. Need an actual last-definition/no-intervening-effective-write dichotomy on the demanded segment and a proof copies preserve remaining demanded readings. NOP creates no source origin.

**Backedge / self-edge.** Labels may not change on a self-loop, so semantic branch events, not label inequality, start visits. The same static site can produce different values on different visits. Fresh visit origins must be absent by a prefix-history invariant. Singleton self selection is valid only after its representative has been initialized and remains the demanded origin; not because a static name was allocated. Entry-to-first-visit and repeated-visit cases must be separate in the induction.

## Ownership and conclusion

The missing proof crosses the old static cut/token, temporal history, original-PHI retention, joint semantic execution and finite-run transport boundaries. A single joint induction owner is necessary; no circular source-only/target-only invariant suffices. The accepted local footprint and proposed paired allocator cannot close this gap by projection. The audit finds no checked counterexample to the frozen contract, but also no existing exported theorem discharging the dynamic segment/readiness implication. Global readiness remains Risk 3; this report does not lower it. Strategist review should choose the actual segment invariant and its supported induction decomposition before any complete-block claim is attempted.
