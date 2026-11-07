# Owner-pair coverage audit (C0.analysis.global.owner_pair_coverage)

This is a source/interface audit, not a proved global separation theorem.
No accepted proof or frozen statement is changed by this note.

## Consumer and proposed obligation

The final consumer is still the memory-relocation invariant described at
concretizeStageSimScript.sml:29-44; there is no formal global relocation
predicate there (the two final proofs remain unfinished). The existing
formal future-demand predicate is joint_byte_demand_def
(frameJointDemandScript.sml:63-67). It observes reads before the same
edge's writes and does not inspect a horizon write. Its concrete witness
is read at j and no source writes to byteA on [n,j).

The following is a **proposed, unproved** allocation/allocation *write*
consumer, not a statement copied from a checked theorem. All displayed
variables are universally quantified. `S` below is a documentation
abbreviation for exactly the conjunction of stage/shape/static premises
in concretize_common_call_activation_disjoint:44-49, with vs0 and lo.
It is not a new HOL predicate or an additional soundness premise.

```
S /\ joint_trace vs0 C q0 es qs q /\ n < j /\ j <= LENGTH es /\
EL j (q0::qs) = JointConfig stkJ PGJ GJ tnJ reader instJ sJ omsJ omJ hsJ hJ /\
byteA IN joint_reads (EL j (q0::qs)) /\ lo <= byteA /\
byteA NOTIN joint_mem_taint (EL j (q0::qs)) /\ ~in_revert_forward reader sJ /\
(!k. n <= k /\ k < j ==> byteA NOTIN joint_writes (EL k (q0::qs)) (EL k es)) /\
activation_cache (EL j (q0::qs)) dA ownerA aidA (bA,szA) /\
bA <= byteA /\ byteA < bA+szA /\
byteB IN joint_writes (EL n (q0::qs)) (EL n es) /\ lo <= byteB /\
activation_cache (EL n (q0::qs)) dB ownerB aidB (bB,szB) /\
bB <= byteB /\ byteB < bB+szB /\
(dA <> dB \/ aidA <> aidB) /\
canonical_metadata C C' (Allocation aidA) pA szA /\
canonical_metadata C C' (Allocation aidB) pB szB
==> pA+szA <= pB \/ pB+szB <= pA
```

This would be sufficient for the distinct-instance portion of preserving
one demanded byte through one competing relocated write. It is not yet
known to cover every simulation obligation. In particular it excludes
writes below lo, external effects not represented by the source footprint,
and same-instance offset reasoning. Proving whole-site disjointness for
arbitrary cached B without an actual relevant write/demand would be too
strong: dead cached allocations may legally share static storage.
For same-instance writes the needed conclusion is unequal relocated
byte addresses, not disjointness of an interval from itself.

## Exact selection interfaces

* `joint_read_owner_birth_above`, frameReadOwnershipScript.sml:52-64:
  trace, initial empty cache, ptr_discipline, no DALLOCA, endpoint j,
  read membership, byte>=lo and nonrevert yield ops,v,b,sz,d,owner,aid,t;
  G lookup selects the site, t<j is allocation_birth and EVERY index
  t<i<=j retains both depth presence and that exact cache binding.
* `joint_demand_owner_birth`, frameDemandOwnershipScript.sml:180-195:
  requires an already selected G lookup; its no-write output begins at
  MAX n (SUC t). It alone does NOT prove t<n.
* `joint_untainted_demand_cache`, frameDemandTaintScript.sml:5-15:
  trace, empty initial cache, n<=j, endpoint selected cache, containment,
  endpoint untaintedness and no writes on [n,j) imply for EVERY n<=k<=j
  both d<=depth(k) and that cache at k. Its proof:18-27 uses
  joint_trace_untainted_alloca_before to derive t<n. This excludes late
  birth and popping/reusing the selected activation under these premises.
* Competing writes: `joint_writes_source_subset`,
  frameWriteOwnershipScript.sml:30-40, puts each expanded edge write in
  source_memory_write_ranges of its current instruction, including resume.
  `access_ok_write_site`:17-27 selects ops,v,b,sz from an above-lo byte,
  access_ok and nonrevert. `joint_provenance_activation_owner`,
  frameDemandOwnershipScript.sml:139-154, selects dB/ownerB/aidB at the
  SAME configuration from the G lookup (current or saved cache).
  `joint_write_owner_identity`, frameWriteOwnershipScript.sml:43-55,
  identifies that site with an explicitly supplied containing cache;
  it is an identity theorem, not independent existence or static liveness.
* `joint_untainted_cache_last_write`, frameDemandLastWriteScript.sml:20-29,
  yields birth t and last actual write m, t<m<j, plus no writes on (m,j)
  and survival on (t,j]. It does NOT give absence of writes on [m,j):
  m itself writes. Any use as a demand start must use SUC m.
* `joint_activation_cache_interval` transports an existing binding forward
  only with presence at every interval index; it cannot select an owner
  backward. `joint_activation_cache_exposure` (frameOpenCall) recovers an
  identical earlier current cache inside an explicit open ancestor call,
  not a no-write interval beginning at the exposure time.

Initial cache emptiness above is discharged from o1_run_state_ok, as in
concretizeAnalysisOwnerDemandScript.sml:105; no zero allocator cursor is
used. ALLOCA has no physical initialization write: joint_writes_call is
empty; frameAllocationEffects' checked allocation facts preserve physical
memory and add fresh-byte taint. B's cache birth by itself is not a
competing write event.

## Exhaustive case matrix

First select A at j as above and restrict attention to the displayed
untainted nonreverting witness. n is always the ORIGINAL comparison
index; never replace it by an exposure time.

| Case and exact hypothesis | Indices / checked coverage / remaining gap |
|---|---|
| byteA<lo or endpoint reverting | Outside proposed allocation-pair consumer. Fixed-region reservation or revert result relation is needed at simulation level; common-call separation does not discharge these. |
| Selected A has szA=0 (or selected write B has szB=0) | Impossible from b<=byte /\ byte<b+size; natural arithmetic forces both selected sizes positive. Metadata containing a zero-size site without byte containment is not excluded generally. |
| A birth tA>=n | Under endpoint cache, containment, untaintedness, empty initial cache and no writes [n,j), excluded by joint_untainted_demand_cache proof / joint_trace_untainted_alloca_before. joint_demand_owner_birth alone is insufficient. |
| A birth tA<n and slot survives [n,j] | Cache and depth at n supplied by joint_untainted_demand_cache. This is the coexisting-owner matrix below. |
| A popped then same numeric depth reused between n and j | Excluded for the selected birth instance by the same birth/survival result; not excluded merely by equal endpoint depths. A call and return wholly ABOVE dA is allowed. |
| B's activation disappears after its write at n | No survival of B to j is needed by the proposed consumer. Both owners are compared at n. Do not transport B to j or identify a later re-entry. |
| B allocation birth is at n | A fresh ALLOCA edge is not a write; cannot be the competing write in the proposed consumer. Cache B must exist before a store through it. Separate relocation/taint ALLOCA step remains necessary. |
| dA=dB and aidA=aidB at n | Same slot at the same index; finite-map functionality identifies the site. Do not demand interval self-disjointness. No-write [n,j) excludes a raw write to byteA at n; generic relocation offset injectivity is the separate required consumer. |
| dA=dB and aidA<>aidB at n | Distinct local sites in one activation. `context_layout_local_local_disjoint` (concretizeLayoutInterference:230-243) gives numeric separation ONLY after both production liveset lookups and nonempty sinter, local item membership, actual layout equation, forced-empty and local/import exclusion are supplied. `concretize_untainted_owner_read_liveset` (OwnerDemand:83-102) gives A membership at its activation_location at n. B is only a write owner, not a future untainted read: corresponding B liveset membership at that location is NOT yet assembled. `joint_local_write_used_generator` (UsedDemand:188-196) gives Used generation for OriginLocal, not the whole LiveAt-intersect-Used certificate. Saved owner and incoming-write cases require projection as well. |
| dA<dB at n | Covered NUMERICALLY by `concretize_common_call_activation_disjoint` (CommonCall:43-62) PROVIDED an actual call c<n at dA with caller=ownerA and depth>dA for c<k<=n is supplied, together with endpoint A cache at depth dA. B cache may be current or saved at n; exact byteB containment and canonical metadata match. The [n,j) interval is unchanged. Selecting that call from arbitrary joint_trace still needs a root-trace/entry or actual call-origin argument; arbitrary q0 may already have a saved caller. |
| dB<dA at n | FIRST UNCOVERED DIRECTION-SENSITIVE semantic integration row. Existing common-call theorem would need demanded ANCESTOR B, but here the demand is for DESCENDANT A. Arithmetic symmetry does not exchange those hypotheses. Need liveset membership of ancestor B at its still-open call, generated by the actual write/access in a descendant (possibly Incoming), paired with imported A membership at that call. No future untainted read of B is supplied. This is not a specialization of the accepted theorem. |

The three depth rows are exhaustive only AFTER coexisting caches at n
and the correct activation identity have been obtained. They are not a
proof of common layout membership. Likewise identical numeric raw bytes
cannot replace the selected instance: ownership uniqueness must be used
before static-id or metadata equality.

## Minimal next integration proposal (unproved)

Prioritize a WRITE-OWNER projection boundary, not another demand-ancestor
specialization: given a genuine open call c<n of ancestor ownerB and an
actual above-lo write at n whose provenance is owned by that ancestor's
cache, derive Allocation aidB membership at the original caller call
location in the ACTUAL stage observation's context_mem_livesets.
Pair it with the accepted descendant import membership for A at n.
The likely missing semantic adapter is Incoming operand ownership/flow
back to the selected ancestor call argument; merely knowing G points to
an ancestor cache does not prove the call's static operand generator.
This proposal needs strategist validation before any theorem skeleton.

Separately, same-activation write generation must supply both halves of
B's liveset at the common location (not Used alone), and an actual call
selection boundary must discharge c for dA<dB when q0 is a root entry.
No claim that these tasks exhaust target-taint converse lifting or
external effects is made here. All accepted numeric helpers remain intact.

## Checked boundary update (E0192 and write-owner checkpoint)

The gaps above record the audit-time state, not the current helper inventory.
The following checked results supersede its call-selection and write-membership
gaps; the proposed numeric consumer itself is still unproved.

* `joint_activation_cache_open_call` in frameOpenCallScript.sml selects an
  actual NONE call c<n at depth d for an endpoint saved cache, with exact
  owner/cache and strict depth survival on (c,n]. It requires
  activation_depth q0<=d; arbitrary traces beginning inside a call remain
  excluded. This closes the explicit call-origin gap in the dA<dB row
  for root traces, without changing the original no-write interval.
* `concretize_write_owner_liveset` in
  concretizeAnalysisWriteLivesetScript.sml:10 exports the actual-write
  membership requested above. Under the same stage/static premises as
  concretize_untainted_local_read_past_write_liveset, an actual reachable,
  nonreverting write of byte>=lo, a containing activation_cache, and its
  activation_location give Allocation aid membership at that location
  in the owner's observed context_mem_livesets. The write is expressed by
  joint_transition/joint_writes, so it is not restricted to ordinary
  store edges. No untaintedness or future read of the writer is required.
* For current owners, store marking inserts write-base locations
  unconditionally, independently of LiveAt. Existing ptr_mark_stores_covers_write
  provides the fold theorem; concretizeAnalysisStoreMark adds only indexed
  instruction and mem_write_ops/BP adapters. Thus the old suggestion that
  local stores need a LiveAt certificate was unnecessary.
* For suspended owners, joint_incoming_production_argument already follows
  nested Incoming origins to a saved Local INVOKE argument and supplies both
  production LiveAt and Used at that call. Simultaneous byte-cache uniqueness
  identifies this owner with the supplied cache; no new ancestry invariant
  is needed. The write-owner proof consumes that interface directly.

Remaining work: assemble the same-depth and ancestor-writer numeric rows
using these memberships and the existing demanded-owner/import interfaces,
while selecting one common actual call and retaining activation identity.
This update does not establish exhaustive numeric separation, same-instance
relocation injectivity, fixed-region/external-effect cases, or converse
output-taint lifting. It changes neither frozen stage statement.
