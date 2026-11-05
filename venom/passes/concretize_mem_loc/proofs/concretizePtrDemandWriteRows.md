# Historical ordinary-write rows (.67.4)

This is a signature audit, not a theorem of suffix exclusion or prefix coverage.
Source checked after E0292 / commit 6374b862f. All indices below refer to the
**same** h,H,w returned by ptr_demand_protected_token_interval; never select w
again with ptr_endpoint_local_interval_exclusion.

## Common witnesses and premise ledger

Fix w<j and j+1<LENGTH h. Set A=EL j h, L=LENGTH A.po_stack,
Hj=EL j H=(ts,r,births,PT,TG,saved,entries), and prefix=TAKE (SUC j) h.
Protected allocation is (token,aid), source (b,sz), placement (pa,sz),
bottom depth d. Destination allocation, when owned, is (tokB,bid), source
(db,sb), placement (pb,sb), bottom depth e. Execution always occurs in
A.po_fn; this is **not** necessarily either owning function.
Bottom depth 0 is oldest; bottom depth L is executing. Thus e<d means
*destination ancestor*, and e>d means *destination descendant*.

| Premise | Actual source supplier / specialization |
|---|---|
| protected owner present at j, cache, token | ptr_demand_protected_token_interval final universal conjunct: d<=L, owner cache aid=(b,sz), EL (L-d) ts=token |
| protected local liveset at j | same theorem's w<t<LENGTH h clause at t=j: Allocation aid in context_mem_livesets of the original protected fn at cursor of ptr_owner_view d A |
| source nonwrite at j | same theorem's w<j and j+1<LENGTH h clause; preserve w |
| source ownership at j | ptr_structural_transcript_ownership at j, unfold ptr_snapshot_ownership_def: ptr_source_ownership vs C prefix A ts r births PT TG saved |
| live destination owner | ptr_transcript_historical_placement with i=j, same snapshot in both positions, FLOOKUP TG v=SOME(tokB,bid), A.po_prov v=SOME(db,sb); gives e, ownerB, outputB, pb, cache, registry and positions lookup |
| numerical/tagged provenance agreement | ptr_source_ownership_prov_erases; address Var selected by op_prov. Lit has no owner tag and is handled as fixed |
| both owners belong to same stack | preceding two rows; no retained endpoint birth alone is used |
| token length/distinctness | ownership -> ptr_source_ownership_caches -> ptr_source_birth_caches_activations -> ptr_source_activations_length and ptr_source_activations_distinct. Length ts=SUC L and ALL_DISTINCT ts. EL injectivity then makes token equality equivalent to d=e |
| original owner function at j | ptr_owner_view at fixed bottom depth, using owner persistence on the protected interval; destination function supplied directly by historical placement and registry lookup. Do not identify activations merely by fn_name |
| actual step / observed context | owner membership from ptr_frame_table_source; source lookup from o1_ctx_shape distinct names; output lookup from historical placement (protected owner from existing endpoint step). ptr_stage_lookup_origin supplies an actual step, ctx_fn_names and o1_walk_view for any selected output lookup |
| concretize success and fn_eom=NONE | actual fn_pass_step via fn_pass_step_def and execute_configured_fn_pass_concretize; EVERY source fn_eom=NONE. No arbitrary layout is introduced |
| static local items | ptr_concretize_static_items provides successful static_alloca_items. ptr_frame_table_source and ptr_table_source_def locate the ALLOCA for the selected local cache; static_alloca_items_ALLOCA_exact / static_alloca_items_MEM locate its item. ptr_frame_sizes (AllocationSize) and ptr_static_alloca_item_size identify runtime and static size |
| output local metadata and position | ptr_frame_current_mems / ptr_frame_saved_mems, or historical placement. ptr_stage_placements_def plus FLOOKUP uniqueness identifies its position with pa or pb, including metadata obtained through imports |
| no local/import key collision | ptr_stage_local_not_imported for each local ALLOCA, using same actual step, source/output lookup, ctx_inst_ids_distinct and callee_first; expand MEM_MAP/is_alloca_op only at this boundary |
| source CFG / owner wellformedness | ptr_history_cfg_analyze_ok and frame/context membership, EVERY wf_function, all_reachable, ssa_form, fn_inst_wf, EVERY inst_wf, fn_ptr_ok from the protected theorem's hypotheses |
| positive sizes | k<sz gives sz>0. For destination, reason under hypothetical target membership: ptr_write_transport_owner_containment implies delta+length<=sb and membership in that range, hence sb>0. Empty target writes close before separation |
| target footprint inside owner interval | ptr_write_transport_owner_containment; needs scalar untainted size, address range from access_ok, placement endpoint below dimword, label/value transport. These are conditional paired-write inputs, not source-success conclusions |
| fixed target footprint below lo | ptr_write_transport_fixed_containment, with access_ok fixed-address bound and scalar untainted operands |

The scalar/untainted-size facts have existing suppliers ptr_write_max_size_untainted,
ptr_write_max_size_no_provenance (WritePurity). Exact transport additionally needs
same labels and CALL/STATICCALL/DELEGATECALL post-returndata **length equality**.
This remains an explicit paired-write premise; maximum containment alone cannot
supply exact footprints. Stage endpoint/word bounds are not needed by separation
itself, but remain required by the transport inputs; this audit does not prove them.

## Six rows

### 1. Fixed destination

No destination owner depth, local item or liveset is needed. Use
ptr_stage_placements_reserved_prefix on (aid,pa,sz), k<sz and
fixed_region_reserved lo C: lo<=pa+k. Fixed containment above says every target
written byte is <lo, a contradiction. Zero-length writes are empty. **Ready**
under the stated paired-write classification/transport inputs, without eom.

### 2. Identical (token,aid)

Historical placement at j and protected interval give the same token and aid;
ALL_DISTINCT ts gives e=d; birth/positions lookups identify db=b, sb=sz, pb=pa.
ptr_write_transport_owner_exact, specialized to k, transports membership in the
actual paired step_writes iff. Its source side contradicts the same-w suffix
nonwrite. No separation or second liveset needed. CALL returndata length equality
must be supplied, not inferred from containment. **Ready**, conditionally on the
exact paired-step inputs. ptr_chrono_write/step_writes matching uses the actual
adjacent source observation, not a separately supplied poststate.

### 3. Same token, different aid, owner active (d=e=L)

fn=A.po_fn, common cursor=(A.po_state.vs_current_bb,A.po_state.vs_inst_idx).
Protected liveset supplied at t=j. For destination, current tagged support
ptr_source_tag_roots_current plus ptr_source_params_fresh_current excludes an
own-token PARAM root; ptr_tag_roots_local_wf gives pointer_derived_vars for bid.
ptr_production_operand_gen / BP scan completeness gives the destination base;
inst_write_op=Var v and ptr_active_write_liveset give its production liveset at
this **same cursor**. Apply ptr_output_local_local_separation with the actual
fn step, both local items, both output tuples, positive sizes and no-import
collision from the common ledger. Containment then excludes pa+k. **Ready at
interface level**; this is the same-w version of the body of the existing
ptr_endpoint_local_interval_exclusion, not a use of its existential conclusion.

### 4. Same token, different aid, owner suspended (d=e<L)

Let n=L-d-1. The executing descendant's TG v=(token,bid) refers to the suspended
owner at EL n stack. Crucial existing supplier:
**ptr_source_tagged_owner_call_liveset** (TaggedCallLiveness, lines 42-81).
It takes precisely source ownership at j, EL(SUC n)ts=token and that TG lookup,
plus owner wellformedness, and concludes Allocation bid's production liveset at
EL n stack's saved INVOKE cursor, for any observed_ctx. Set observed_ctx to the
protected owner's actual observed.cu_context. Protected liveset is already at
that cursor. Both items and tuples are local to that original owner, not to the
executing descendant. Apply ptr_output_local_local_separation as in row 3.
**Ready at interface level**. There is no missing suspended-destination liveness
axiom: the exported call-liveset theorem is exactly the needed supplier.

### 5. Destination owner below protected owner (e<d)

Destination owner is the ancestor. Set n=L-e-1, desc=(ptr_owner_view d A).cf_fn,
ds=(ptr_owner_view d A).cf_state and top-relative k'=L-d; e<d implies k'<=n.
The ancestor local item is Allocation bid with tuple (pb,sb). Protected aid is
imported into the destination owner's actual observed context.
**ptr_output_tagged_ancestor_destination_separation** (TaggedCallLiveness,
lines 84-131) already packages this orientation: instantiate its aid=bid,
sa=sb, pa=pb, bid=aid, sb=sz, owner=tokB, v=destination variable, t=j,
prefix=TAKE(SUC j)h, tokens=ts. It calls the call-liveset supplier for the
ancestor's local destination, then ptr_output_suspended_descendant_separation.
The latter obtains the protected descendant's imported tuple and common-cursor
imported liveset via ptr_frame_descendant_import / ptr_frame_descendant_demand.
No protected liveset is required in the ancestor's local map: it is the imported
side there. The resulting existential protected position must be identified as
pa via stage placements/coherent metadata, not chosen anew. Disjointness may
then be used symmetrically. **Ready at interface level**; swapping interval
arguments *alone* would have been wrong, but the exported tagged-ancestor theorem
supplies the formerly suspect local-demand premise.

### 6. Destination owner above protected owner (d<e)

Protected owner is ancestor. Set n=L-d-1, desc=(ptr_owner_view e A).cf_fn,
ds=(ptr_owner_view e A).cf_state and k'=L-e<=n. Use
ptr_output_suspended_descendant_separation with local Allocation aid,
local tuple (pa,sz), descendant allocation bid with cache (db,sb), t=j.
Its local liveset premise is exactly the protected theorem's t=j output.
Its imported destination tuple and imported demand at the same saved INVOKE
cursor are provided internally by ptr_frame_descendant_import and
ptr_frame_descendant_demand, not by the descendant's executing operands.
Identify the returned imported pb with the global positions lookup.
All other premises are the common ledger above. **Ready at interface level**.

## Completed/sibling activations and verdict

For an ordinary owned destination, historical placement at i=j gives its token
in ts at a live owner index. The protected owner is in that **same** ts by the
same-w interval bridge. ALL_DISTINCT ts and total ordering of their bounded
indices yield precisely rows 2-6. A retained birth from a completed sibling
cannot replace either witness; such births alone give no row. Re-entered
functions do not collapse tokens. No name inequality argument is needed.

No missing production *liveset* implication was found for the six rows:
the strict-ancestor and same-token/suspended cases already have exports in
TaggedCallLiveness. Thus the specific reason keeping .67.3 Risk 3 (unmatched
ancestor local demand) is resolved by this audit. Recommend a scoped Risk-2
integration with explicit paired ordinary-write hypotheses and the exact same w.
This recommendation is not a checked HOL exclusion theorem. In particular it
does not discharge operand classification, word-endpoint bounds, actual paired
post-returndata equality, or source-step success from the frozen task antecedent;
those must not disappear when formulating the integration theorem. If .67.3 is
intended to establish any of those rather than consume them, that larger claim
remains Risk 3 and requires separate strategist guidance.
