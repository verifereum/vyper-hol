# Production-layout / chronological-ledger interface audit

Scope: C1.5.90.11. This is a dependency audit, not a theorem or a claimed
noninterference invariant. Source references below are relative to this directory.
No executable definitions or frozen statements are changed.

## Exact checked interfaces

| Layer | Existing boundary and actual result | Remaining consumer obligation |
|---|---|---|
| Endpoint origin | `ptr_endpoint_protected_history` (ProtectedHistory:31–55): under actual `ptr_chrono_history`, empty initial cache, source WF/SSA/shape/no-DALLOCA, access_ok at each history observation, ordinary non-revert endpoint, selected operand provenance SOME(b,sz), owner depth d/cache aid, and an untainted x in that site, returns w with `w+1<LENGTH h`, `ptr_chrono_write C x (EL w h)`, no later source write before the endpoint, retained owner-cache interval, `ml_used_gen (Allocation aid) bp mems` at w and `ml_read_gen` at endpoint. | Discharge ordinary endpoint / operand selection / owner-localization from the constructed source partner. This theorem does not handle an initial fixed byte or exceptional endpoint. |
| Production propagation | `ptr_endpoint_protected_livesets` (ProtectedLivesets:8–43) adds actual stage, observed context, function lookup/output step, global id and call order facts, ptr discipline and exact production bp/mems; returns a w and for EVERY `w<t<LENGTH h`, `FLOOKUP (context_mem_livesets (concretize_memloc_fuel fn) observed.cu_context fn bp (cfg_analyze fn)) (Allocation aid)=SOME xs` and membership of the owner-view cursor at t in xs. | This bridge IS ALREADY PROVED. Do not schedule a duplicate semantic-demand-to-liveset proof. Its substantial stage/metadata premises must be derived at the global use site. |
| No-kill / canonical intersection | `ptr_owner_context_liveset` (OwnerConflict:55–71): used seed at u, read seed at r, owner alive u..r, u<=t<=r, actual production bp/mems/sizes, CFG correctness and no `ptr_ml_can_kill` t..r imply production liveset membership at t. ProtectedLivesets uses `ptr_stage_owner_interval_no_kill` to discharge no-kill retrospectively from no actual write of x. | Do not replace no-kill by arbitrary analysis convergence. Sorted canonical live/used intersections and marking are inside the existing proof. |
| Write seed | `ptr_owner_context_store_conflict` (OwnerConflict:105–128) adds `MEM b (find_base_allocas_opt bp (inst_write_op owner_inst_t))` and returns liveset membership of BOTH allocations at the same owner cursor. `ptr_fuel_liveness_covers_write` (StoreCoverage) marks writes independently of read propagation. | Identify the actual write address owner and connect it to the syntactic write base set; an arbitrary tag or equality of numerical sites does not discharge this. |
| Local placement | `ptr_production_completed_local_local` (ProductionSeparation:201–215): fn_ptr_ok, static items, exact production candidate and successful completion, local/import key separation, distinct positive-size items, two canonical livesets sharing addr and two completed lookups imply `reserved_intervals_disjoint (pa,sa) (pb,sb)`. `ptr_output_local_local_separation` (LayoutOutput:135–151) exposes this using actual output metadata. | Show demand and write refer to distinct allocation ids in the SAME activation; derive metadata sizes/positions from actual stage. |
| Combined local boundary | `ptr_endpoint_local_store_separation` (ProtectedSeparation:7–53) already combines endpoint last writer, production liveness and completed placement. Returns w and disjointness at each later event with `po_fn=fn`, `d=LENGTH po_stack` and `MEM other (find_base_allocas_opt bp (inst_write_op inst_t))`, for two supplied distinct local static items/positions. | This is stronger than a standalone liveness proposal, but still only interval disjointness conditional on write-base classification. It has no target history or footprint statement. |
| Cross-frame placement | `ptr_output_suspended_descendant_separation` (CallSeparation:8–39): at actual history event t, suspended owner frame n, descendant frame k<=n with cached bid, exact stage/observed metadata, positive sizes and owner local allocation live at saved INVOKE cursor imply an imported metadata witness `(Allocation bid,pb,sb)` AND disjointness from owner local `(pa,sa)`. | Prove owner tokens correspond to these coexisting frames and derive which one is ancestor. Imported pointer used by the current callee must be resolved relative to its original owner, not the active callee. |
| Byte consumer | `ptr_chrono_last_writer_agreement` (OperationalBytes:39–50): two ACTUAL histories, equal index n bounded in both, and for each x in live a w<n with immediate post-write byte equality and BOTH source and target write-footprint exclusion for w<k<n, conclude `ptr_bytes_agree` at n. | Target exclusion is a premise, not a conclusion. Also this consumer uses synchronized indices; actual deletion/call alignment needs an index-map generalization or an explicitly constructed padded history, NOT a silent substitution of unequal history indices. |

## Fuel fallback and retained candidates

ReadCoverage:217–223 is a valid warning about deriving semantics from ordering
alone, not a counterexample to ProtectedLivesets. The latter uses the actual
`concretize_memloc_fuel fn`, not arbitrary fuel=0. ProductionSeparation separates
candidate pair separation (`ptr_production_candidate_local_local` and
`ptr_production_candidate_local_import`) from completion. Completed-local-local
uses `ptr_completion_pair_separation`; local-import additionally distinguishes
missing candidate (fresh checked completion) from retained candidate. Thus no
argument may say successful completion makes ALL positions disjoint. Reuse is
legal unless production livesets conflict. Forced positions are empty via
fn_ptr_ok in these proofs. Local/import id noncollision remains an explicit
premise, to be derived from stage/global distinct-id and import metadata facts.

## Missing semantic bridge, split by ownership

The smallest useful next boundary is an **event-level target write-footprint
classification/containment theorem**, parameterized by the existing actual
source ownership, actual aligned source/target instruction and operand relation,
and actual production registry metadata. Its conclusion should classify EVERY
target written byte as either an identity fixed-region byte or
`pos(owner,aid)+offset`, `offset<size`, with a corresponding source written byte
`base(owner,aid)+offset`. This must be a reverse/exhaustive classification, not
only a source-to-target inclusion. No target noninterference, endpoint agreement
or future demand belongs among its hypotheses.

Why needed: `ptr_ledger_write_pair` (PrefixLedger:16–28) gives only
`source step_writes -> target step_writes` inclusion and immediate agreement on
untainted source-written bytes. That implication permits additional target
writes. It cannot imply exclusion of a demanded target byte. The MSTORE macro
constructs events but does not strengthen this direction or derive operand
agreement. Its rho is store-relative; endpoint relocation is owner-relative;
consistency on the selected site's bytes must be derived, not assumed globally.

After classification, the event exclusion proof has these distinct cases:

1. Same (token,aid): natural offsets below the actual site size give injective
   `pos+offset`. If translated demand byte is written, the corresponding source
   x is written, contradicting the last-writer interval. A saturated nat
   subtraction formula without in-site bounds does not establish injectivity.
2. Different local ids, same token: use ProtectedSeparation's combined boundary,
   disjoint production intervals, and exhaustive target footprint containment.
   Mere equality of po_fn/stack depth is not evidence of activation identity.
3. Different simultaneously live tokens: identify ancestor relation from actual
   ownership/registry and frame stack. Apply CallSeparation at the suspended
   owner's saved INVOKE cursor (reverse which owner is suspended as needed).
   Imported sites retain the original token, so a write through an imported
   ancestor pointer is case 1 or an ancestor-local comparison, not automatically
   a descendant allocation. Need a checked localization theorem ensuring every
   positive-byte live write/demand tag has such an active owner; persistent
   births alone also contain retired tokens and do not imply co-liveness.
4. Fixed-region vs owned: needs identity relocation and layout reservation
   separation derived from fixed_region_reserved/stage metadata. None of the
   local/local theorem premises states this case. Initial fixed bytes also need
   an initial agreement sentinel rather than an allocated last writer.
5. Zero-length writes have empty footprints and require no allocation numerical
   uniqueness. Positive-byte classification implies positive site size. Ghost
   tags for zero-size sites must not be identified by numerical-site inversion.

## Proposed integration contract (schema only, NOT a new theorem)

Given actual stage data, source ownership history, a source endpoint selected
owned byte, ProtectedLivesets/ProtectedSeparation's last-writer interval, and an
actual paired aligned intervening event with established variable/operand
relocation, derive target footprint exclusion at that event. First prove the
exhaustive write classification boundary above for the authorized instruction
class; then discharge same-owner and interval-disjointness cases using existing
libraries. The global prefix invariant must CONSTRUCT operand relocation,
registry metadata, chronological alignment and write pairs; they are not
consequences of the currently bare PrefixLedger definitions. A new global
coverage theorem must not take a source partner or noninterference as a premise.

Current unresolved obligations: exhaustive write transport, live owner-token
localization, fixed/owned placement boundary at use, exceptional endpoints,
index-map last-writer consumer, and construction of global operand agreement.
Existing local stage placement and protected production liveness should be
reused without duplication. This audit certifies neither their unprovided
premises nor the two frozen stage theorems.
