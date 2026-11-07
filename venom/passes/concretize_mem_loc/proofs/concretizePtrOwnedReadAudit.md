# Owned-byte recovery revalidation (.46)

## Status and scope

This replaces the stale .29/.30 completion assessment. The companion theory
builds the current prerequisites and typechecks `owned_read_recovery_candidate`.
It is a quotation, **not a theorem**. No recovery, universal prefix coverage,
source continuation success, fixed-byte recovery, or extra opcode producer is
claimed. Existing conditional diagnostic theorems are retained unchanged.

### Checked follow-up (.48-.50)

Actual step/adjacent/interval framing and full actual-writer retention are now
proved (E0403/E0404). The .50 in-place migration replaces the requested writer
clauses of `ptr_demand_interval` with actual writes and successor purity.
`ptr_paired_actual_protected_write_exclusion` proves the formerly quoted
`actual_protected_exclusion_candidate` with its exact assumptions and the SAME
supplied w. DemandWriteExclusion, HistoricalWriteExclusion, HistoricalMcopyExclusion,
PairedJumpSchema and this audit consumer all rebuild. The missing-boundary and
migration discussions below describe the earlier diagnostic, superseded by
these checked exports; endpoint byte recovery itself is still not proved.

The recovery quotation now uses the **input** (first conjunct) of the old
`ptr_demand_interval_def`, written explicitly without its requested-writer
witness. It includes the existing task-derived shape, access/provenance and
owner placement interfaces. It does not assume a writer, immediate equality,
matching rho, target exclusion, or a future source step. `w` and `token` are
not inputs to this quotation. Its conclusion remains

```
read_byte (b+k) endpoint.po_state.vs_memory =
read_byte (pa+k) at.po_state.vs_memory
```

These input interfaces are conditional on an already constructed paired prefix;
this audit does not prove their global supplier from an arbitrary target run.

## Index discipline (one transcript throughout)

Write x=b+k, y=pa+k, N=LENGTH h-1, T=LENGTH done. Source history ends at
EL N h=endpoint; target history ends at EL T ht=at, with LENGTH ht=SUC T.
For a retained source initializer w, select q0<T with EL q0 done=w.
The ledger record is (w,q0,rho). Its content agreement and owner certificate
refer to **EL(SUC w)h, EL(SUC q0)ht, EL(SUC w)H**. They do not refer to
EL(SUC q0)(done++[N]), the next normalized source sample.

`ptr_structural_trace_gap_memory` relates immediate source successor memory to
that normalized sample, but does not replace the owner snapshot or purity
index. No gap normalization is needed if source framing runs directly from
SUC w to N. Target framing runs from SUC q0 to T. A later target event j
satisfies q0<j<T and hence w<EL j done by the embedding's strict order.

## Current supplier matrix

All SML paths below are in this directory unless otherwise indicated.

| Link | Exact current boundary and consumer | Assessment |
|---|---|---|
| Actual initializer | `OwnedActualInitializer:6`, `ptr_endpoint_owned_actual_initializer`: history, initial empty allocas, no-DALLOCA history, live endpoint owner lookup containing x, endpoint purity => exists w with SUC w<LENGTH h, actual step_writes membership at w, purity at SUC w, no actual writes for w<n and SUC n<LENGTH h, and owner lookup/depth throughout w<=n<LENGTH h. | **Proved.** Instantiate x=b+k. k<sz supplies containment. This already avoids the requested CALL ambiguity. |
| Same initializer plus protection | `ProtectedLivesets:107`, `ptr_endpoint_actual_protected_livesets`: explicit input interfaces in the new quotation => exists w with those same actual membership/purity/exclusion clauses, liveset membership at every w<t<LENGTH h, owner lookup/depth and non-forwarding throughout w<=n<LENGTH h, and ml_used_gen at w / ml_read_gen at endpoint. | **Proved.** Select w ONCE from this stronger theorem, not independently from two existential selectors. `ActualWrites:112` (`ptr_stage_owner_actual_interval_no_kill`) is its actual-aware no-kill supplier. |
| Stable token / historical birth | `ptr_transcript_bottom_token_interval` as used by `DemandWriteExclusion:81-91`; transcript ownership at each index; `ptr_source_ownership_caches`, `ptr_source_birth_caches_slices`, `ptr_birth_slices_def`. | Existing suppliers. Apply bottom-token interval to [w,N], using depth presence from actual protection, then endpoint snapshot to identify token. The public `ptr_demand_protected_token_interval` still selects a REQUESTED writer and cannot be used unchanged to select w. Actual-demand packaging is not installed. |
| Retention in done | `ptr_structural_transcript_erasure` -> trace; trace constructors root/gap/pair (`StructuralTrace:11-49`) retain every departed event except NOP. `ptr_structural_trace_nop_interval:258` covers gaps after retained events only. | **Proved.** `ptr_structural_trace_actual_writer_retained` in HistoricalWriteExclusion exports this exact coverage via strong trace induction. Apply after transcript erasure. It includes leading and trailing gaps and done=[]. Gap appends only NOP, whose actual footprint is empty; pair appends the departing index. This supplies index existence only, not ledger equality or target exclusion. |
| Ordinary writer | `WriteClassification:106`, `ptr_step_write_opcode`: actual membership => opcode in [MSTORE;MSTORE8;ISTORE;MCOPY;CALLDATACOPY;RETURNDATACOPY;DLOADBYTES;CODECOPY;EXTCODECOPY;CALL;STATICCALL;DELEGATECALL;DRET]. | Existing route, not inference from nonemptiness alone. Exclude DRET using `ptr_discipline_no_dret` with reachable observation and source shape, as HistoricalWriteExclusion already does. Remaining opcodes are nonterminator and non-INVOKE. |
| Ledger completeness | `PairedFields:104-114`, `ptr_paired_writes_def`: q0<T, ordinary source instruction, nonempty actual footprint => exists rho with MEM (EL q0 done,q0,rho) ws. `ptr_paired_write_event:162` retrieves the record. | **Available once retention is proved.** Nonempty follows from the selected x actually belonging, not from a requested range. |
| Immediate byte equality | `ptr_paired_write_def:91-102` -> `ptr_ledger_write_pair_def` (PrefixLedger:16): equality outside source successor memory taint on actual source written bytes. | **Available at SUC w/SUC q0.** Both actual membership and purity are supplied by actual protection, for the SAME w. |
| Matching relocation | `ActiveWriteOwner:7`, `ptr_paired_write_owner_relocation`: owner certificate on xs and immediate snapshot, x IN xs, lo<=x, ptr_birth_slices post tokens births, length tokens=SUC stack length, active geometry, live owner lookup containing x and positions lookup => rho x=pa+(x-b). | **Proved.** post=EL(SUC w)h, snapshot=EL(SUC w)H, xs=actual footprint at w; owner depth d and lookup come from protection. Slices/length from historical ownership; geometry from source reachability/no DALLOCA and empty initial table. Since x=b+k, result is pa+k. No retained-birth global uniqueness is needed or valid. |
| Source actual suffix exclusion | `ptr_endpoint_actual_protected_livesets`, no actual write after w. | **Proved.** Supplies the source interval frame premise for SUC w<=n<N. |
| Target actual suffix exclusion | `HistoricalWriteExclusion:318`, `ptr_paired_historical_owned_write_exclusion` requires `ptr_demand_interval ... w`, whose second conjunct includes no later REQUESTED chrono writes. | **Proved after in-place actual-demand migration.** `ptr_demand_interval` now records actual membership, immediate successor purity and actual suffix nonmembership. The existing owner/layout/separation cone and historical assembly rebuild against that interface. `ptr_paired_actual_protected_write_exclusion` in the companion audit theory checks the exact formerly quoted candidate, packaging the SAME supplied w via bottom-token continuity. No requested-nonwrite implication is used. |
| Actual chronological byte frame | `OperationalBytes:7,30,71` all consume REQUESTED exclusion. Compiler `stepWriteFootprintBase:107,128,148` also uses requested capacity, not clipped actual length. | **Proved (E0403).** `ActualByteFrame` exports `ptr_chrono_step_actual_byte_frame`, `ptr_chrono_history_actual_byte_frame` and `ptr_chrono_history_actual_interval_byte_frame`, imported by the audit. These consume actual `step_writes` exclusion, including clipped external calls and internal return callee memory. Old requested interfaces remain intact. |
| Endpoint assembly | Frame source SUC w -> N and target SUC q0 -> T; combine ledger equality and rho equation. | Routine only AFTER actual exclusion migration, writer retention and actual framing. Not yet proved. |

## Missing boundary statements and exact instantiations

The companion quotations are proposed statements only. Every free variable of
`actual_protected_exclusion_candidate` is to be universally quantified (standard
HOL theorem universal closure); the three smaller candidate statements have
explicit quantifiers in the quotation. None is an invariant definition or axiom.

1. **Writer coverage** is `actual_writer_retention_candidate`, with trace,
   SUC w<LENGTH h and x in actual footprint at w as its only premises.
   Instantiate the erasure of the paired transcript and x=b+k; obtain q0.
   Existing gap theorem alone misses both initial NOPs and the empty-done case.
   Constructor induction handles initial and final NOP-only portions uniformly.
2. **Actual step frame** is `actual_chrono_byte_frame_candidate`:
   forall ctx a z x, chronological step and actual nonmembership imply byte
   preservation. Its fold is `actual_interval_byte_frame_candidate`, forall
   vs ctx h endpoint x i j, history, i<=j<LENGTH h and actual exclusion on
   [i,j) imply read_byte at j equals read_byte at i.
   Instantiate (vs,C,h,endpoint,x,SUC w,N) on source and
   (vs,C',ht,at,y,SUC q0,T) on target. Frame statements are independent of
   stage, positions, ownership or future execution.
3. **Actual protection -> target exclusion** is the full typed
   `actual_protected_exclusion_candidate`. It takes the new recovery inputs
   together with exactly the SAME w's actual/protected output, and concludes
   y outside the actual target write at each q<T with w<EL q done. It assumes
   neither equality nor exclusion in target memory. Token continuity is
   intentionally not an extra premise: derive it from transcript and depth
   continuity. Instantiate x=b+k and j=EL q done in historical classification.

The smallest *semantic* missing boundary is (2), including clipped calls.
Coverage (1) is finite structural elimination. Separately, (3) is a genuine
consumer-interface migration, not discharged merely by adding actual framing.
It should reuse current separation/classification proofs in place, not create
synonym versions of all layout facts. The precise old bottleneck is
`ptr_demand_same_owner_write_exclusion` (DemandWriteExclusion:287-317):
it equates actual source membership with ptr_chrono_write at j, then uses
no-requested-writes from ptr_demand_interval. For actual demand, use source
actual nonmembership directly with `ptr_write_transport_owner_exact` and the
already available source/target successor returndata-length equality
(`ptr_paired_samples_post_returndata`). Other-owner separation consumes the
same protected livesets, stable token and owner cache witnesses, supplied by
actual protection plus transcript. This audit has NOT verified all downstream
proofs after such a migration and does not claim it is already complete.

## Framing constructor audit

`ptr_chrono_step` has four constructors (ChronologicalHistory:29-72):

* **next:** ordinary successful step, post changes only instruction cursor.
  For non-call opcodes `step_writes_def` is exactly requested ranges; existing
  `step_inst_base_OK_byte_frame` applies. CALL/STATICCALL/DELEGATECALL are the
  only clipped exceptions and need the stronger actual-length byte frame.
* **block:** successful terminator followed by enters_block. `enters_block_memory`
  preserves memory (PHIs update variables only). Call clipping is irrelevant
  for a terminator. The requested OK frame handles the step itself.
* **call (INVOKE):** setup_callee_shared_fields and enters_block_memory show
  memory is shared unchanged; the requested footprint is empty. Do NOT
  confuse this constructor with an external CALL ordinary step.
* **ret:** internal return step, merge_callee_state, adopt_return_fmp,
  bind_outputs, cursor increment. `merge_callee_shared_fields` selects
  **callee s_end memory**, not saved caller memory. adopt_return_fmp_memory
  and bind_outputs_shared_fields preserve it. Existing
  `step_inst_base_IntRet_byte_frame` handles the return step. This is not an
  unexplained memory reset; no equality to an old caller snapshot is needed.

For external CALL/STATICCALL, `exec_ext_call_def` and consume_call_outcome_eq
write TAKE(output capacity) co_returnData, and post.vs_returndata is that
co_returnData. Thus actual length is MIN capacity (LENGTH post.vs_returndata).
`wmwe_byte_at_outside` / `read_byte_write_memory_with_expansion` give byte
framing outside that exact length. DELEGATECALL uses extract_venom_result;
`extract_venom_result_memory` supplies the corresponding TAKE write and
post returndata length. Existing compiler call frame lemmas deliberately
forget this precision by bounding LENGTH TAKE by requested capacity; they
cannot consume actual exclusion in the clipped tail. These underlying memory
facts are adequate primitives, but the chronological lifting is not exported.
No existing actual-aware frame theorem was found by searching venom SML.

## Adversarial checks / preserved historical evidence

`audit_call_clipped_byte` remains a checked CONDITIONAL theorem: with matching
oracle outcome returning one byte, capacity two at offset zero, byte 1 is
requested but not actually written, preserves memory, and retains its previous
taint status. This disproves the *inference* from a later requested writer to
actual initialization, not the frozen task. It is not a concrete EVAL stage
counterexample. Accordingly the old requested-writer recovery input was
removed rather than falsely identifying it with the selected actual writer.

`audit_retained_write_owner_ambiguity` states the FORMER owner formula
explicitly: two retained births can cover byte zero while choosing different
positions. It is not a claim against the repaired active-membership predicate.
The active-owner elimination now resolves that historical gap at the actual
successor snapshot; no further birth-uniqueness conjecture is proposed.

`actual_initializer_candidate` is retained as an historical quotation whose
requested strengthening is now supplied (and strengthened) by ActualWrites.
`mstore_write_producer_candidate` is historical: .45 now proves
`ptr_mstore_write_producer` and `ptr_paired_prefix_mstore` in MstoreProducer.
Importing that theory here validates the current complete nonempty producer;
it is not evidence of arbitrary writing-opcode or prefix coverage.

Fixed bytes x<lo and the initial identity sentinel remain separate future
recovery scope. Other nonempty opcode producers and universal source-success
construction remain unresolved and are not authorized by this diagnostic.
