# Fixed-byte recovery audit (.52)

## Scope and result

This is a bounded interface audit, NOT a proof of fixed recovery, universal
prefix coverage, or the frozen static-memory theorem. The companion
`concretizePtrFixedReadAuditScript.sml` contains only typechecked quotations.
The accepted owned recovery theorem is unchanged. No positions-rewrite fact
is restated here.

The first missing semantic bridge is **fixed target actual-write reflection**.
A ledger write pair supplies only source-to-target footprint inclusion, not
its converse. Thus an empty source footprint does not, from the ledger alone,
exclude a target write to a fixed byte. Existing exact transport and reserved
placement facts look sufficient ingredients outside revert forwarding, but
there is not yet an installed fixed-byte historical assembly theorem.
Do not assume this missing bridge as a new invariant conjunct.

## Expanded endpoint candidate (typechecked, not proved)

```
ptr_paired_prefix R lp positions lo vs C C'
  h endpoint ht at done tokens registry births PT TG saved entries H calls ws /\
ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
  (o1_walk_view rpolicy 2) C C' /\
o1_ctx_shape C /\ o1_run_state_ok vs /\
EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
mem_inv raw_mem_ok C vs /\
fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
EVERY ssa_form C.ctx_functions /\ ~ctx_has_dalloca C /\
ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
EVERY all_reachable C.ctx_functions /\
EVERY fn_defs_reach_uses C.ctx_functions /\
max_live_eom C' = SOME eom /\
x < lo /\ x NOTIN endpoint.po_taint.t_mem ==>
read_byte x endpoint.po_state.vs_memory = read_byte x at.po_state.vs_memory
```

This is the SAME paired-prefix interface as owned recovery, with all
owner-specific arguments and metadata witnesses removed. It asks only for
fixed-byte equality, not global equality of initialized memories. `names`
is a witness for the frozen existential. The frozen statement itself has
not been edited. No source writer, target exclusion, arbitrary relocation
agreement, or future source execution is an input.

## Finite supplier table

| Row | Existing exact supplier | Remaining work / consumer |
| --- | --- | --- |
| 1. Last actual source writer and successor purity | `ptr_chrono_step_actual_mem`: `ptr_chrono_step ctx a b ==> !x. x IN a.po_taint.t_mem /\ x NOTIN b.po_taint.t_mem ==> x IN range_bytes (step_writes a.po_inst a.po_state b.po_state)`. `ptr_chrono_last_actual_interval` selects a last actual write but REQUIRES an earlier tainted byte. | Fixed initial bytes may already be pure, so the owned fresh-allocation selection theorem is inapplicable. Need the finite last-write/no-write dichotomy quoted below; choose maximum actual write and propagate purity backwards through nonwrites. Consumed by ledger lookup and source suffix framing. |
| 2. Writer retention and ordinary classification | `ptr_structural_trace_actual_writer_retained` supplies `q` with `q<LENGTH done`, `EL q done=w` for an actual writer with `SUC w<LENGTH h`. `ptr_stage_observation_no_dret`, reachability from the transcript, opcode cases and `step_writes_def` exclude DRET and the remaining terminating/INVOKE writer cases. `ptr_paired_writes_def` then supplies `MEM(w,q,reloc) ws`; `ptr_paired_write_event` exposes its certificate. | Available proof ingredients, as exercised by owned recovery lines 63–93. No new writer-retention lemma proposed. In particular a source requested CALL range is NOT sufficient to select w. |
| 3. Fixed relocation identity | `ptr_paired_write_owner_byte` gives `(x<lo /\ reloc x=x)` OR an **active** token birth `(base,sz)` with `k<sz`, `x=base+k`, `reloc x=pos+k`. Transcript ownership gives caches/slices (`ptr_source_ownership_caches`, `ptr_source_birth_caches_slices`, `ptr_source_birth_caches_activations`, `ptr_source_activations_length`). | Missing small geometry assembly quoted below. For the second disjunct convert token membership to an actual frame cache, then use `allocas_from lo` on that frame to contradict `x<lo`. Retained births without active membership would not suffice. The existing owned relocation theorem requires `lo<=x`, so cannot simply be applied here. Consumer: immediate ledger equality at source/target successor states. |
| 4. Later target actual-footprint exclusion | `ptr_write_transport_fixed_exact` equates ACTUAL byte sets for scalar pure offset/size, eval-presence equality, labels equality, descriptor and equal returned lengths on CALL/STATICCALL/DELEGATECALL. `ptr_paired_samples_post_returndata` supplies successor return-data equality across NOP gaps. `ptr_historical_write_classification` supplies fixed scalar pure destination or a bounded owned destination, but requires source access/taint and **not in_revert_forward**. `ptr_stage_placements_reserved_prefix` gives `lo<=p+k` for `k<sz` with actual stage, EVERY fn_eom NONE, shape, callee_first, reservation, placements and lookup. | Main missing assembly: target fixed-write reflection quoted in companion. Fixed branch uses actual exact equality (including MIN clipping); owned branch uses relocation containment and the reserved-prefix theorem to contradict target x<lo. Classification also needs derived structural/taint/opaque-use facts, descriptor/eval witnesses and instruction correspondence. Existing historical owned exclusion is for `pa+k`, NOT x<lo, and is not the missing theorem. Revert-forward cases require explicit handling; candidate has no EVERY no-revert premise. |
| 5. Initial entry memory and no-writer framing | `ptr_structural_trace_source` and `_target` provide both chronological histories from the same `vs`. Root rule uses `ptr_chrono_history vs C [a] a` and the analogous target history. `ptr_paired_initial_sentinel` is only `ptr_bytes_agree {x|x<lo} I vs.vs_memory vs.vs_memory`. `ptr_chrono_history_actual_interval_byte_frame` frames actual nonwrites over any `[lo,hi]` within one history. | Need initial-memory projection quoted below, from chronological entry/setup/enters_block memory preservation. If no source write exists, reflection rules out every target write, then frame both histories from index 0. Sentinel is an origin, not agreement at endpoint. |
| 6. Endpoint assembly | `ptr_chrono_history_end` gives nonempty history and LAST endpoint; `LAST_EL` converts to index LENGTH-1. `ptr_chrono_history_actual_interval_byte_frame` consumes `!k. low<=k /\ k<high ==> x NOTIN range_bytes(step_writes...)` and yields endpoint/low byte equality. `ptr_ledger_write_pair_def` gives `ptr_bytes_agree (actual_source_bytes DIFF successor_taint) reloc source_post_mem target_post_mem`. | In writer branch use row 3 and pure successor to get equality immediately after w/q. Use last-source-write maximality plus reflection and strictly increasing done to exclude all target events after q. Frame both suffixes. No-writer branch uses row 5. Transitivity gives the candidate. Not implemented or certified here. |

## Exact proposed boundaries

All names below denote quotations, not installed theorems. Their fully
parsed HOL forms are in the companion theory.

1. `fixed_last_actual_writer_candidate` has only
`ptr_chrono_history vs C h endpoint /\ x NOTIN endpoint.po_taint.t_mem`
as premise. Conclusion is either no actual source write at any
`SUC n<LENGTH h`, OR an actual write w with `SUC w<LENGTH h`, pure successor,
and no actual writes at later `w<n /\ SUC n<LENGTH h`.
This removes the earlier-taint hypothesis of the owned selector without
pretending every fixed byte has a writer. Proof is finite maximum selection
plus `ptr_chrono_step_actual_mem`; allocation metadata is irrelevant.

2. `fixed_write_owner_identity_candidate` is exactly:
```
ptr_paired_write_owner lo positions (reloc:num -> num) xs
  (tokens,registry,births,PT,TG,saved,entries) /\
x IN xs /\ x < lo /\ ptr_birth_slices post tokens births /\
LENGTH tokens = SUC (LENGTH post.po_stack) /\
(!d. d <= LENGTH post.po_stack ==>
  allocas_from lo (ptr_owner_view d post).cf_state) ==>
reloc x = x
```
Its historical premises must come from the SAME writer successor snapshot.
`ptr_history_observation_allocas_from` supplies a realized-history version;
for an arbitrary active frame, recover its frame reachability from the
chronological observation and the stack invariant, then instantiate
`ptr_discipline`. Do not infer cache lower bounds merely from birth retention.
Zero-size births cannot witness `k<sz`.

3. `fixed_actual_write_reflection_candidate` has the full stage/task/paired
antecedent of the expanded endpoint candidate (without endpoint purity),
`x<lo`, `q<LENGTH done`, and target actual membership at q. Its conclusion is
```
x IN range_bytes (step_writes (EL (EL q done) h).po_inst
  (EL (EL q done) h).po_state (EL (SUC (EL q done)) h).po_state)
```
This is an implication to prove, not a supplied exclusion assumption. It
serves BOTH the last-writer suffix and the no-source-writer branch. Check
nonordinary transfers separately; never use the one-way ledger inclusion
in reverse. The companion has the expanded antecedent, with no new invariant
predicate hiding this obligation. Outside revert forwarding, the expected
argument is row 4. Inside revert forwarding, inspect the allowed block
instruction list and paired controls before claiming classification applies.
If an extra no-revert premise proves necessary, this candidate is too strong
and the endpoint/frozen-contract integration needs strategist review.

4. `history_initial_memory_candidate` is exactly:
```
ptr_chrono_history vs C h endpoint ==>
(HD h).po_state.vs_memory = vs.vs_memory
```
No extra entry-agreement hypothesis. Both histories have the same initial
`vs`, so this yields the initial equality needed by the no-writer branch.

## Adversarial checks and dependencies

- A fixed byte can have no writer at all. A theorem demanding a writer is
  false even for a root singleton history; keep the disjunction.
- A CALL requesting two bytes but returning one writes only one byte. The
  checked `audit_call_clipped_byte` in OwnedReadAudit already demonstrates
  this. Reuse that evidence; no duplicate CALL probe was added. Exact actual
  transport, not requested containment, is required for reflection.
- Ledger inclusion alone permits extra target writes; it does not prove
  reflection. Paired sample core fields do not equate memory. These are
  interface gaps, NOT counterexamples to a reachable staged program.
- Reused completed allocations are not the geometry supplier for row 3:
  write ownership has active-token membership, and lower bounds must be
  obtained at the writer successor. No use of vs_alloca_next=0.
- Reserved-prefix theorem was checked against its exact source: it really
  derives `lo<=p+k`, via the reserved interval containing p+k and disjointness.
  It needs k<sz, hence positive size. Neither placement base nor a retained
  birth alone is a sufficient substitute.
- No new opcode producer is authorized by this audit. Universal source
  success, remaining ledger producers, and the frozen static-memory proof
  remain unproved.

## Verification

`holbuild(targets=["concretizePtrOwnedReadAuditTheory"])` passed before this
work. `holbuild(targets=["concretizePtrFixedReadAuditTheory"])` passed after
renaming the quotation's relocation variable (`rho` is an imported constant).
All companion quotations parse/typecheck; none assert the missing claims.
