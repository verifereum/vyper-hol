# Owned-byte recovery audit (C1.5.90.67.29)

## Scope and checked artifact

`concretizePtrOwnedReadAuditScript.sml` contains a compiler-checked quotation
`owned_read_recovery_candidate`, not a theorem. It copies the full antecedent of
`ptr_paired_historical_owned_write_exclusion` through the positions lookup,
removes the arbitrary target event q, and asks for

```
read_byte (b+k) endpoint.po_state.vs_memory =
read_byte (pa+k) at.po_state.vs_memory
```

The candidate is conditional on an **existing** paired prefix. No universal
prefix coverage, source continuation success, or fixed initial-sentinel
recovery is asserted. Historical write exclusion was accepted as E0372 and
committed as 428ff631e. This audit does not change the invariant.

## Exact supplier chain and gaps

All paths below are relative to this directory unless marked otherwise.

| Link | Existing interface | Result / remaining implication |
|---|---|---|
| Source last writer | `concretizePtrDemandWriteExclusionScript.sml:97-145`, `ptr_demand_interval_def` | Gives `w+1 < LENGTH h`, `ptr_chrono_write C (b+k) (EL w h)` and no such writes for `w<j`, `j+1<LENGTH h`; endpoint byte is untainted, `lo<=b+k`, `k<sz`; demanded token/cache remains present for every `w<=j<LENGTH h`. |
| Meaning of writer | `concretizePtrChronologicalHistoryScript.sml:132-137`, `ptr_chrono_write_def` | Exactly ordinary/non-INVOKE, successful step, and membership in **requested** `source_memory_write_ranges`. It does NOT give actual `step_writes` membership. |
| Retention in done | `ptr_structural_transcript_erasure`; `concretizePtrStructuralTraceScript.sml:105` (`ptr_structural_trace_embedding`) and `:258-266` (`ptr_structural_trace_nop_interval`) | Trace only drops NOP events. Writer is ordinary and NOP requested range is empty. Need a finite coverage elimination: `w+1<LENGTH h /\ writer ==> ?q. q<LENGTH done /\ EL q done=w`. Existing nop-interval statement bounds gaps after each retained event; induction must also handle leading NOPs and final trailing NOPs. No ready writer-coverage export was found. |
| Ledger completeness | `concretizePtrPairedFieldsScript.sml:104-114`, `ptr_paired_writes_def` | For `q<LENGTH done`, ordinary source event, and actual source footprint nonempty, gives `?rho. MEM (EL q done,q,rho) W`. `ptr_paired_write_event` at :162-167 retrieves its predicate. Ordinary premises come directly from writer; **nonempty actual footprint does not**. |
| Immediate agreement | `concretizePtrPairedFieldsScript.sml:91-102`, `ptr_paired_write_def`; `concretizePtrPrefixLedgerScript.sml:16-29`, `ptr_ledger_write_pair_def` | Agreement is exactly on `range_bytes(step_writes src pre srcpost) DIFF srcpost.po_taint.t_mem`, between immediate successor states `(EL(SUC w)h)` and `(EL(SUC q)ht)`. Need both `(b+k)` actual membership and postwrite untaintedness. Endpoint purity alone is not a syntactic supplier of either. Requested CALL ranges may exceed clipped actual footprint; even an event with a nonempty actual footprint need not actually write the demanded byte. |
| Relocation identity | `ptr_paired_write_owner_byte`, `concretizePtrPairedFieldsScript.sml:128-138` | For an actual byte gives fixed identity or `?tok bid base size pos off. off<size /\ x=base+off /\ rho x=pos+off /\ FLOOKUP births(tok,bid)=SOME(base,size) /\ FLOOKUP positions(Allocation bid)=SOME(pos,size)`. Fixed branch is excluded by `lo<=b+k`. Owned branch does **not** state that tok is currently active or equals demand token. |
| Same owner | `ptr_structural_transcript_ownership`; `ptr_source_ownership_caches`; `ptr_source_birth_caches_slices` / `ptr_source_birth_caches_active_lookup` (`concretizePtrActivationBirthsScript.sml:297,313`); `ptr_active_alloc_unique_owner` (`concretizePtrAllocationOwnershipScript.sml:110-116`) | Demand cache/token at `SUC w` supplies the demanded birth. Active unique-owner theorem compares two lookups in the **active states list**. Arbitrary ledger owner lookup in retained births is not known active: `ptr_birth_slices_def` (:35-39) is active-to-birth equality, not an inverse. `ptr_birth_token_bound_def` only bounds token by history length. Missing: uniqueness of every retained positive-byte birth against an active demanded birth, or another supplier identifying ledger rho with demand relocation. Do not infer this from existential ownership. |
| Source suffix frame | `ptr_chrono_history_interval_byte_frame`, `concretizePtrOperationalBytesScript.sml:71-78` | Given history, `lo<=hi`, `hi<LENGTH h`, and no requested range membership for `lo<=k<hi`, yields byte equality between indices hi and lo. Set lo=`SUC w`, hi=`LENGTH h-1`; chronological endpoint supplies LAST h=endpoint. Demand excludes chrono writes, not ranges directly. Ordinary success gives range exclusion for ordinary steps. Terminator/INVOKE requested ranges need the existing opcode/range facts. No actual footprint equality is needed on source suffix. |
| Target suffix exclusion | `ptr_paired_historical_owned_write_exclusion`, `concretizePtrHistoricalWriteExclusionScript.sml:318-339` | Full stage/demand/paired antecedent plus `w<EL q done`, `q<LENGTH done` gives `pa+k NOTIN range_bytes(step_writes (EL q ht).po_inst (EL q ht).po_state (EL(SUC q)ht).po_state)`. Covers all departed events after writer; endpoint is target index `LENGTH done` (done has one entry per departed target event). |
| Target suffix frame | `ptr_chrono_step_byte_frame` (:7-10), `ptr_chrono_history_byte_frame` (:30-34), `ptr_chrono_history_interval_byte_frame` above | These take **requested** exclusion, not actual exclusion. They cannot consume E0372 for CALL. Need actual-footprint byte framing for an actual chronological step, then its interval fold through target index `LENGTH done`. Frozen `venom/compiler/stepWriteFootprintBaseScript.sml:107-110` (`exec_ext_call_byte_frame`) also assumes requested range exclusion, so is not this missing boundary. |
| Gap normalization | `ptr_structural_trace_gap_memory` (:334) and `ptr_event_embedding_gap_byte_frame` (`concretizePtrEventEmbeddingScript.sml:43-50`) | The first transports immediate source successor memory across NOP gaps; the second requires requested exclusion. Neither replaces immediate postwrite purity/actual membership nor fixes rho identity. Do not use a later sampled source snapshot as the write-owner snapshot. |

## Minimal unresolved interfaces (not new assumptions)

The chain is **not integration ready** from currently exported interfaces.
Three independent semantic links remain before a boring endpoint assembly:

1. A demanded last requested writer must supply an actual untainted ledger
   byte at its immediate successor, or the writer selection must be revised
   to select the actual initializing write. This includes CALL clipping.
   It cannot be discharged by nonempty footprint alone. Any revision would
   affect demand selection (`ptr_chrono_initializing_writer_seed`,
   `ptr_demand_protected_token_interval`, `ptr_demand_interval_exists`) and
   their lifetime/liveset consumers, not just the final recovery theorem.
2. The ledger rho must match the demanded token/allocation byte, despite
   arbitrary existential ownership over retained births. A sufficient
   geometric theorem would compare an active positive-byte birth to *all*
   retained births. Current active-only uniqueness is weaker. If that is
   false, repair belongs to paired-write owner certificates and all write
   extension suppliers, not an extra hypothesis on recovery.
3. Actual-footprint chronological byte framing (including CALL) must feed
   an interval fold. Requested-footprint framing cannot use E0372.

Retention and post-taint propagation also need checked elimination lemmas,
but their intended supplier cones are explicit above. No new demand
restriction has been imposed; in particular no equality of endpoint memories,
matching rho, actual writer membership, or target exclusion was silently added
to the quoted candidate. No counterexample to the frozen task is claimed.

## Fixed bytes

`ptr_paired_initial_origin` and `ptr_paired_initial_sentinel` concern `x<lo`
with identity relocation. The demand here explicitly has `lo<=b+k`, so neither
is the origin for this owned-byte proof. Fixed initial memory and its sentinel
require a separate future recovery argument.
