# Relocation consumer interface audit

Diagnostic output for C0.relocation.consumers.binding.audit. These are candidate
interfaces, NOT additional stage hypotheses or proved simulation facts. The
checked numerical/temporal interfaces do not certify the missing producers.

## Checked interfaces

| Boundary | Existing producer |
|---|---|
| Total memory observation | `joint_memory_observation q a` uses `read_byte a s.vs_memory`, including its implicit zero tail |
| Temporal agreement | `demand_agree (joint_relocation_demand lo positions q0 es qs n) (joint_memory_observation q) (joint_memory_observation qt)` |
| Current read / retained demand / entry identity | `joint_relocation_demand_current`, `joint_relocation_demand_retained`, `joint_relocation_demand_initial_agreement` |
| Writer exemption | `joint_relocation_demand_nonrevert`, using `joint_trace_nonrevert_read_at` |
| Numerical write/read noncollision | `concretize_relocation_write_demand_noncollision`; conditional on its explicit metadata/position bridge |
| Simultaneous update | `demand_agree_update`, `demand_agree_producer_update`; produced values may depend on pre-state |
| Raw provenance erasure | `origin_frame_maps`: `origin_erase om = G` and `LIST_REL (\f om0. origin_erase om0 = f.cf_prov) stk oms` |
| Local origin/cache connection | `local_cache_ok`: local origins have a matching `vs_allocas` entry; this does NOT resolve parameter origins |

## Candidate state fields (exact clause shapes)

Free symbols below are parameters, not definitions hidden behind a purported
simulation theorem. Use one source trace globally: an allocation's first birth
index is a possible token; a bare activation depth or static instruction ID is
not. An ALLOCA revisiting its cached site keeps its token. Calls need their own
activation lifetime token so a popped depth can later be reused safely.

* Control: `s.vs_current_bb = st.vs_current_bb /\ s.vs_inst_idx = st.vs_inst_idx /\ s.vs_prev_bb = st.vs_prev_bb`.
  Function/instruction alignment is a separate pass relation; it must allow
  inserted dead allocations for clients such as LowerDload, not require identical
  instruction lists in the reusable call lift.
* Resolved origins: `resolved : (string, num # (num # num)) fmap` with
  `SND o_f resolved = G`. The number denotes a lifetime token, NOT `OriginLocal`
  or `OriginParameter`. Local-origin and parameter-origin resolution into this
  map are separate missing theorems. Maintain saved maps plus a resolved parameter
  vector; resolving an `OriginParameter k` follows the caller operand witness.
* Scalars, using existing bytewise agreement:
  `!v x y. FLOOKUP G v = NONE /\ lookup_var v s = SOME x /\ lookup_var v st = SOME y ==> word_agree_except (op_taint tn (Var v)) x y`.
  This needs a separate definedness/lookup-domain correspondence: conditional
  agreement alone is vacuous if the target variable is absent.
* Pointers (candidate modular equation):
  `!v token b sz x y. FLOOKUP resolved v = SOME (token,(b,sz)) /\ lookup_var v s = SOME x /\ lookup_var v st = SOME y ==> y = n2w (target_base token) + (x - n2w b)`.
  Here x,y have type bytes32, and target_base has type num -> num. No natural
  offset precision is asserted for arbitrary affine arithmetic.
* Comparisons: modular translation alone does not preserve LT/GT. Need concrete
  bounds at the compare use site: for both operands, offsets in [0,sz], and
  `b+off < 2**256 /\ target_base token+off < 2**256`. Inclusive one-past pointers
  need explicit attention; a bound only on accessed bytes is insufficient.
  `access_ok` supplies same-site source ranges; target nonwrapping is MISSING.
* Memory: checked demand agreement above, plus target taint transport on demanded
  observations. Do NOT require agreement on every currently cached byte.
* Observable state: accounts equal except source taint at the current address,
  other addresses equal; use `storage_agree_except tn.t_stor` and
  `storage_agree_except tn.t_trans` at that address. Immutables use equal domains
  and `word_agree_except {b | (k,b) IN tn.t_imm}` at each key. Logs, request shape,
  context, outcomes and pending deletions require their own equality clauses.
  Request snapshots use `request_agree_except D`; dead_wf transports D through
  source-indexed agreement. Output-taint inclusion must be proved separately.

## Producers by transition boundary

| Field | Entry | Ordinary / PHI / terminal | Call | Return |
|---|---|---|---|---|
| control, definedness | identical input state; entry block alignment | per-instruction and PHI matching MISSING | setup_callee projections; callee selection MISSING | bind_outputs arity, restored caller and incremented index; matching MISSING |
| resolved origins | empty maps/cache | ALLOCA birth/cache reuse and affine/PHI resolution MISSING | evaluate args and resolve parameter vector MISSING | restrict saved caller map; outputs must have no pointer provenance |
| scalar/pointer values | identity, no origins | taint byte transport / modular affine rules MISSING | args scalar or relocated pointers; tainted args forbidden by taint_ok | outputs scalar and untainted; byte/definedness binding MISSING |
| memory | checked initial agreement | simultaneous update algebra + numeric noncollision available; produced bytes and actual write translation MISSING | shared observations preserved by setup; finite demand across push needs adapter | shared callee memory via merge; demand across pop needs adapter |
| observable agreement/taint | equal input, entry_taint | stores, external effects, return and revert MISSING | frame-local vars reset; shared tn retained | shared observable fields from callee; caller vars restored/restricted |

Concrete call/return references: `origin_frame_reachable` call rule pushes om,
sets callee om=FEMPTY, passes `MAP (op_prov G) ops`, clears t_var and G. The
PARAM origin subsequently is `OriginParameter k`, not a resolved caller token.
The return rule restores `DRESTRICT caller_om (COMPL (set outputs))`, similarly G
and t_var. It does not propagate a callee-origin return value into caller G.
`ptr_use_ok` rules out pointer RET uses; `taint_ok` rules out tainted call args
and tainted RET operands. Their consequences need explicit boundary lemmas.

`setup_callee` copies shared memory/observables, clears vars and cache, and sets
params=args and return_pc_token=LAST args (or zero). The last argument may need
a nonpointer classification; do not silently assume return tokens agree if a
relocated pointer can occupy that slot. `merge_callee_state` copies memory,
accounts, transient, returndata, logs, outcomes, requests, pending deletions and
immutables, while preserving caller vars/cache/control. `adopt_return_fmp` only
changes fmp; no-DALLOCA and fn_ptr_ok restrictions must justify ignoring its
numerical difference, not assume allocator equality.

## Explicit missing numeric and semantic interfaces

The metadata producer needed by the checked noncollision helper is exactly:

```sml
!k d owner aid base size. k <= LENGTH es /\
  activation_cache (EL k (q0::qs)) d owner aid (base,size) ==>
  canonical_metadata C C' (Allocation aid) (positions owner aid) size /\
  lo <= positions owner aid
```

It must be DERIVED from frozen hypotheses (including fixed_region_reserved),
not passed to either frozen wrapper as a new hypothesis. No checked producer
of the lower-bound conjunct has been identified in this bounded audit.

Actual write coverage is separate from numerical noncollision. For ordinary
matched source/target steps with source footprint W and target footprint WT,
the required coverage shape is:

```sml
!z. z IN WT ==> ?a. a IN W /\ relocation_pair lo positions q a z
```

Allocation birth must be handled separately: joint_writes excludes
ALLOCA. `exec_alloca_def` updates the cache and output, NOT memory; fresh-zero
values must not be assumed (the memory's implicit tail is zero only when unread
addresses lie there). Future untainted read lifetime/birth machinery
prevents demanding fresh untouched bytes, but that does not prove the target
step's byte-production rule. External-call writes and return memory need their
actual `step_writes` boundaries. Do not put coverage inside the state relation.

## Two reachability directions

Forward terminating-run matching is the consumer for ctx_sim_dead. For
stage_taint the existing definition quantifies over ALL target reachable frames
at request-producing ordinary steps and over ALL target final_taint witnesses.
A necessary separate interface is:

```sml
frame_reachable vs C' stkt PGt Gt tnt fnt it st ==>
  ?stk PG G tn fn inst s.
    frame_reachable vs C stk PG G tn fn inst s /\
    frame_match stk PG G tn fn inst s stkt PGt Gt tnt fnt it st
```

`frame_match` is an UNDEFINED CANDIDATE relation, not a proved fact. Its local
request and halt clauses must match the relevant target event back to a source
event and bound tnt.t_stor/t_trans/t_imm and target ret_taint by the source
bounds, with dead_wf moving D across agreement. Existential forward termination
alone establishes none of this. The generic call lift must expose both
directions (or a justified deterministic-prefix reflection interface).

## Numeric producer audit (C0.relocation.consumers.producers.numeric)

The target comparison bound is already stronger than the earlier audit found:
`concretize_canonical_numeric` in `concretizeLayoutNumericScheduleScript.sml`
proves `p + sz < dimword (:256)` from the stage, `o1_ctx_shape`, source
`fn_eom = NONE`, and `canonical_metadata C C' a p sz`. Hence EVERY offset
`off <= sz`, including one-past, satisfies `p + off < dimword (:256)`.
No liveness, convergence, or extra stage premise is needed for this numeric
consequence. The metadata bridge and identification of the comparison's
resolved token with that canonical site are still necessary. Source comparison
ranges come from `access_ok_def`; actual operands are words, so their `w2n`
values are already below dimword. An offset witness is `w2n x - b` when
`b <= w2n x <= b + sz`. This does not assert nonwrap for arbitrary affine
intermediate values.

The same numeric theorem proves, for POSITIVE `sz`,
`EVERY (reserved_intervals_disjoint (p,sz)) C.ctx_global_reserved`.
Together with `fixed_region_reserved lo C`, this gives `lo <= p`: if
`p < lo`, take the reserved interval covering byte p; either disjointness
alternative contradicts `pos <= p < pos + size` and `0 < sz`.
This is a direct natural-arithmetic boundary lemma to extract, NOT a new
stage assumption. Its precise reusable signature is:

```sml
fixed_region_reserved lo C /\ 0 < sz /\
EVERY (reserved_intervals_disjoint (p,sz)) C.ctx_global_reserved ==>
lo <= p
```

### Metadata and position selection (still to implement)

* `activation_cache_source_static_item` in `concretizeAnalysisRuntimeItems`
  supplies `?items. static_alloca_items owner = SOME items /\
  MEM (Allocation aid,sz) items`, from reachable joint config, initial
  `o1_run_state_ok`, `o1_ctx_shape`, global distinct IDs, cache membership,
  and a byte witness `b <= byte /\ byte < b+sz`.
* That proof also derives `MEM owner C.ctx_functions` using erasure and
  `frame_history_cfg_invariant`, but exports only the static item. Exporting
  the membership boundary, or strengthening that existing theorem in place,
  avoids copying the history proof into each consumer.
* `concretize_context_local_numeric_find` supplies a position and a FIND
  entry for an owner's own item from its successful context transformation.
  `concretize_stage_lookup` supplies that transformation plus output lookup
  and the observed context. These facts are sufficient for
  `canonical_metadata_def` using the source owner, items, and output.
* Define/select `positions owner aid` from that owner's transformed
  `fn_mems_used` FIND entry, with an arbitrary default outside the certified
  domain. The bridge cannot hold for an arbitrary unconstrained positions
  function. `canonical_metadata_unique` (global distinct IDs) reconciles
  imported metadata with this chosen position.
* `joint_trace_edge_at` supplies joint reachability at noninitial indices;
  index zero requires the trace entry reachability boundary. Do not omit
  this case by imposing `k > 0` on a final consumer.

### Domain caveat for the previously proposed bridge

The bridge quantified over ALL cache entries, whereas the existing runtime
item producer requires a byte witness and the reservation-avoidance theorem
is conditional on positive size. `exec_alloca_def` caches zero sizes too;
`exact_static_alloca_size_def` and `collect_static_allocas_def` also accept
zero. Thus neither cited theorem by itself proves the all-cache bridge.
This is an interface gap, NOT a checked counterexample to either stage theorem.
For write/demand noncollision the cache entries extracted from
`relocation_pair_def` have an in-interval byte and therefore positive size;
the economical consumer refinement is a byte-scoped (or positive-size)
bridge. Comparison pointers can refer to a zero-size site; they need the
canonical metadata/nonwrap conjunct, but not reservation separation of an
empty interval. A full cache-to-item boundary without positivity can instead
use `o1_frame_source_sizes_lookup` / `o1_frame_source_sizes_saved` and exact
static instruction collection, generalizing `source_alloca_sizes_positive_item`
in place rather than adding a duplicate near-variant. This remaining proof
must be owned explicitly before treating all-cache metadata as established.

No frozen wrapper or executable/contract definition was changed by this audit.

## Value/origin producer audit (C0.relocation.consumers.producers.values)

This section specifies unproved local interfaces, not a state simulation.
The concrete transition rules audited are `origin_frame_reachable` entry,
next, block, call, ret and `origin_out/step/phis` in `frameOriginUpdates`.

### Lifetime representation and adversarial transition checks

A convenient candidate token is `(activation_birth_index, aid)` rather than
raw `(b,sz)` or stack depth. The activation birth is zero for entry and the
successor trace index for each call. Carry a stack of activation births in
parallel with the saved frames. Within an activation, the cache never deletes
an ALLOCA entry, so revisiting aid reuses the token. Distinct calls at reused
depth get distinct birth indices. A local token still denotes its allocation
while suspended, even when a callee holds a PARAM alias to it. A numeric
encoding can be introduced later if required; no uniqueness by address is used.

At each activation carry two witness maps/vectors:

* a local cache-token table `ct : (num, token # (num # num)) fmap`;
* resolved parameter vector `rp : (token # (num # num)) option list`.

A schematic resolution boundary, with `om` the EXISTING tagged origin map and
`rv` the candidate resolved variable map, is:

```text
resolve_tag ct rp (OriginLocal aid, site) = lookup ct aid,
  with any returned entry required to have the same site;
resolve_tag ct rp (OriginParameter k, site) = EL k rp,
  guarded by k < LENGTH rp and equality of the returned site;
resolve_tag ct rp (OriginDynamic, site) = NONE (no DALLOCA domain).
forall v. FLOOKUP rv v = OPTION_BIND (FLOOKUP om v) (resolve_tag ct rp).
MAP (OPTION_MAP SND) rp = PG.
```

All the notation above is specification only.
Require full resolution on the origin domain, so `SND o_f rv = G`;
partial resolution alone would silently drop pointer equations.

| Transition challenge | Required producer, not yet proved |
|---|---|
| first ALLOCA | insert `(current_activation,inst_id)` in ct with the actual post-cache `(b,sz)`; origin_out labels it OriginLocal |
| cached ALLOCA | preserve ct token and site; `exec_alloca_cached_site` and `local_cache_ok` provide existing cache boundaries, not token uniqueness |
| repeated calls at same depth | push activation birth, ct, rp, rv; allocate a new activation birth on every push, never derive it from depth |
| PARAM passed to PARAM | resolve caller `Var` via caller rv, then `MAP` those operand witnesses into callee rp; callee PARAM follows rp, not callee ct |
| PHI | selected incoming operand resolves against PRE-entry om/rv; `origin_phis` writes outputs in the tail map but `origin_phi` always reads the original om (parallel semantics) |
| return output restriction | restore saved ct/rp/activation and `DRESTRICT saved_rv (COMPL outputs)`; `origin_frame_reachable_ret` exports no callee pointer provenance |

Exact algebraic boundary shapes to implement after definitions are approved:

```text
resolution ct rp om rv ==> resolution ct rp
  (DRESTRICT om keys) (DRESTRICT rv keys)
resolution ct rp om rv /\ resolve_tag ct rp tagged = SOME resolved ==>
  resolution ct rp (origin_set om [v] (SOME tagged))
                   (rv |+ (v,resolved))
resolution ct rp om rv /\ op = Var v /\ FLOOKUP om v = SOME tagged ==>
  FLOOKUP rv v = resolve_tag ct rp tagged
```

The cache, parameter-vector and PHI cases require more than these algebraic
facts. In particular the existing `origin_frame_maps` only erases tags; it
cannot manufacture lifetime resolution. `origin_frame_current_lookup` and
`origin_frame_saved_lookup` export tags but do not resolve them.

### Value and definedness boundaries

Require `!v. (lookup_var v s = NONE <=> lookup_var v st = NONE)` separately
from conditional value equations. For one-output updates the reusable
boundary is: equal lookup domains before update implies equal domains after
`update_var v x` and `update_var v y`, even when x and y differ. Simultaneous
PHI evaluation needs equal chosen predecessor labels and definedness of all
selected PRE-state operands, not sequential updates of the pre-map.

Scalar byte agreement is `word_agree_except (op_taint tn op) x y` with output
taint produced by the real instruction rule. Untainted scalar operands then
agree exactly. Pointer equations are modular:
`y = n2w (target_base token) + (x - n2w b)`; copying preserves that equation.
For ADD/SUB the nonpointer operand must agree exactly and affine restrictions
must select the legal pointer position (especially SUB). `fn_ptr_ok` supplies
`affine_pointer_ops` and forbids Label arithmetic, but these clauses still
need operand-facing elimination lemmas. Do not use natural offset containment
for intermediate arithmetic. The old proof's local `word_displ_add` and
`word_displ_neg` already contain the polymorphic group algebra; generalize/
export one reusable displacement lemma and refactor those callers, rather
than adding another near-duplicate.

Returns remove output provenance; it remains to prove via `ptr_use_ok` and
origin-to-syntactic-pointer coverage that RET operands cannot carry resolved
pointers. `taint_ok` similarly supplies untainted return/call operands only
after its opcode disjunctions have been eliminated. Neither is automatic
from the restriction rule alone.

### ALLOCA byte and taint production (correction to earlier audit)

`exec_alloca_def` NEVER writes or zero-initializes memory: fresh case changes
`vs_allocas`, `vs_alloca_next`, and one variable; cached case changes just the
variable. Thus the byte-production boundary is unchanged total `read_byte`
at EVERY source address, and unchanged target memory for a matched constant
assignment. Fresh-byte ZERO is NOT an implementation fact. At birth,
`mem_taint_def` unions `new_site_bytes` into tn.t_mem (then subtracts actual
step writes); `out_taint` of ALLOCA is empty. Cached reuse adds no new bytes.
The target constant assignment has no cache birth and no new-site taint, so
source freshness can justify the target-taint subset, not equality. The
remaining boundary is demand-lifetime transport across birth, plus pointer
output relocation and variable-domain agreement. Proving zero memory contents
is neither necessary nor supported by the actual ALLOCA definition.

## Execution producer audit (C0.relocation.consumers.producers.execution)

### Hidden return token: equality is not justified

`setup_callee_frame` exports `vs_return_pc_token = LAST args` (or zero),
but `fn_invoke_ok` checks only the callee Label, not the last argument's
classification. `ptr_use_ok` permits a pointer at ANY argument index provided
that index is in P nm. Thus do not assert LAST args equality. The earlier
scalar candidate needs a separate opaque-return-PC class: `RETPC_PARAM`
reads the hidden token even though `origin_out` gives it no provenance.

The actual frozen shape contract offers a different derivation path:
`o1_fn_shape` includes `fn_shape_ok`, which includes `opaque_use_ok` and
`retpc_shape_ok`. By `opaque_use_ok_retpc_use`, RETPC_PARAM-derived variables
may only flow through ASSIGN/PHI or the final operand of RET/RETFMP/DRET
(`retpc_use_ok_def`). The last operand is discarded by RET (`FRONT ret_vals`);
RETFMP/DRET are excluded by fn_ptr_ok. A scalar relation excluding
`retpc_var fn v`, with equal lookup domains but opaque values in that class,
is therefore the candidate interface. Opaque copies/PHIs, callee token setup,
and RET FRONT erasure each need their own producer. This is a design path,
NOT a proved noninterference theorem. No checked stage counterexample follows
from token inequality alone; the opaque-use restrictions must be respected.

### Actual write/byte boundary (schematic unproved obligations)

For matched ordinary steps, write `W = range_bytes (step_writes i s s1)`
and `WT = range_bytes (step_writes it st st1)`. These are step results, NOT
fields assumed in a state invariant. The required boundary is:

```text
step_inst fuel C i s = OK s1 /\ step_inst fuelt Ct it st = OK st1 ==>
  (!z. z IN WT ==> ?a. a IN W /\ relocation_pair lo positions q a z) /\
  (!a. a NOTIN W ==> read_byte a s1.vs_memory = read_byte a s.vs_memory) /\
  (!z. z NOTIN WT ==> read_byte z st1.vs_memory = read_byte z st.vs_memory)
```

The implication also needs the candidate operand relation, opcode alignment
and access hypotheses; it is not claimed for arbitrary i,it. Produced-byte
agreement must be demand-scoped, not on all W:

```text
post_demand a z /\ a IN W /\ z IN WT ==>
read_byte a s1.vs_memory = read_byte z st1.vs_memory
```

Derive it per opcode from related untainted bytes and address/length
translation. MSTORE uses bytewise word agreement; MCOPY uses PRE-state
source observations and handles overlap simultaneously; read-byte tail zero
must be preserved through the observation interface, not list-index bounds.
External-call return writes need identical request/outcome control and a
matched return-copy footprint; length truncation cannot be silently ignored.
ALLOCA and transformed constant ASSIGN have empty W/WT and unchanged memory;
new-site taint and post-demand transport remain separate obligations.

Observable boundaries additionally preserve request shape, logs, addresses,
pending deletions, halted/control outcomes and equal domains of immutables;
accounts/transient/immutable payloads agree outside source taint. Request
snapshots are PRE-call, so request taint consumption must use pre-state tn,
not step_taint. Reverting continuations use `joint_read_exempt` and the checked
nonrevert-demand lemma; do not derive ordinary read equality for their payloads.

### Generic frame lifting, not identical instruction lists

A reusable interface should parameterize a function/control alignment, a
relocation of allocation tokens, and local step obligations. Push:
`setup_callee` resets vars/cache, stores args, resets predecessor/control and
copies shared observations. Pop: `merge_callee_state` copies memory, accounts,
transient, returndata, logs, outcomes, requests, pending deletions, immutables;
it restores caller control/vars/cache by starting with saved caller state.
`bind_outputs` requires equal output/value arities and folds zipped updates;
`adopt_return_fmp` only changes fmp, with existing `adopt_return_fmp_allocas`
and frame projections. Keep fmp/allocator values out of observable equality;
fn_ptr_ok/no-DALLOCA must prove their numerical difference unobserved.

The generic local interfaces need distinct ordinary, block/parallel-PHI,
push, pop, halt and abort clauses. Terminal clauses must preserve result
kind (with the allowed Revert exemption), and bind related return VALUE
vectors after FRONT removal. They must NOT demand equality of the discarded
return-PC token. Frame relation stacks save resolved origins and parameter
vectors, caller taint variables and opaque classifications.

Allow an aligned step to match a finite nonempty sequence on the other side,
plus explicit silent insertion steps preserving observations, if clients may
insert dead ALLOCAs. A prefix-reflection proof with zero-step matches needs
a well-founded rank preventing infinite stuttering; control alignment alone
is not such a rank. Concretize's same-length instruction replacement may use
one-step alignment, but the generic call lift must not bake it in.

### Forward and target-prefix obligations and induction indices

Forward: induct on a finite source execution derivation/trace length, using
entry alignment and per-boundary extension to build a target prefix. A
terminating source result needs a related terminal target result. Arbitrary
execution fuel is not a syntactic instruction-count index: recursive INVOKE
runs also consume fuel, so a separate adequacy lemma must choose target fuel.

Reverse: induct on the target `frame_reachable` derivation (or its finite
history length), reflecting entry/next/block/call/ret to a source prefix.
Entry witnesses use the same input vs, context entry lookup, block-entry
alignment and initial taint; target entry PHIs cannot be waved away in a
generic client. In the concrete task first_block_no_phi simplifies this.
Silent target insertions require the rank/alignment boundary above.
Reachability reflection must preserve matched REQUEST/HALT witnesses, not
just match the resulting active state:

```text
target reachable st /\ target ordinary OK step adds request ==>
  source reachable s /\ source ordinary OK step adds matching request /\
  target pre-taint stor/trans SUBSET source pre-taint stor/trans /\
  source/target pre-snapshot agreement outside D

final_taint vs Ct sth tnt Rt ==>
  ?sh tn R. final_taint vs C sh tn R /\
    tnt.t_stor SUBSET tn.t_stor /\ tnt.t_trans SUBSET tn.t_trans /\
    tnt.t_imm SUBSET tn.t_imm /\ Rt SUBSET R /\
    dead-observable agreement of sh and sth
```

Each displayed schema includes existential source witnesses; it is not an
additional hypothesis permitted on the frozen wrappers. `taint_within_def`
has exactly the request stor/trans and final stor/trans/imm/return clauses
shown. `final_taint_def` is reachable non-INVOKE Halt plus step_taint and
ret_taint; merely reflecting an active instruction misses its post-taint.
`dead_wf` transports the dead sets from the source storages/immutables/
returndata to the target only AFTER the corresponding agreement is proved.

All these execution clauses remain implementation obligations. Clean builds
of the existing boundaries do not establish a full opcode or generic call
simulation. The strategist must now turn the three audits into explicit
producer implementation components before final stage work is authorized.

## Endpoint and local-integration audit (2026-11-05)

This ledger supersedes any implication above that strict endpoints or the
cache-to-layout bridge are already discharged. It adds no theorem premise.
Validated existing targets: frameRelocationMemoryOpaque, CopySteps,
StoreValues, LoadSteps, AllocationSteps, ScalarSteps, AffineSteps,
CompareSteps, Phi; frameActivationSeparation; concretizeAnalysisStageSizes,
RuntimeSizes; concretizeLayoutNumericSchedule; frameRelocationRangeGeometry.
All passed holbuild (audit evidence in episode dossier).

### Source strict endpoint: preservation machinery already exists

`joint_reachable_cache_separated` (frameActivationSeparation:177) gives
`frame_cache_separated stk s` from joint reachability and an empty INITIAL
cache. It does not require a zero initial frontier.
`frame_cache_separated_local` gives `alloca_inv s`, whose
`alloca_next_valid_def` bounds every current cached `(b,sz)` by
`b+sz <= s.vs_alloca_next`. `frame_cache_saved_bound` (same file:190)
already gives the SAME bound for every saved frame at index k. Thus a new
cache-history induction is unnecessary! `activation_cache_def` combines
these two cases. `joint_trace_prefix_reachable` supplies reachability of
all prefix configurations.

The raw endpoint adapter is now proved as `joint_activation_cache_strict`
in `frameRawEndpoints`. Its interface uses the weaker explicit empty-cache
premise instead of `o1_run_state_ok`, and requires `EVERY wf_function`
(the prefix-adequacy well-formedness premise). The previous intended shape was:

```sml
mem_inv raw_mem_ok C vs0 /\ o1_run_state_ok vs0 /\
joint_config_reachable vs0 C
  (JointConfig stk PG G tn fn inst s oms om hs h) /\
activation_cache (JointConfig stk PG G tn fn inst s oms om hs h)
  depth owner aid (b,sz) ==> b + sz < dimword (:256)
```

`joint_reachable_raw_frontier` now composes `joint_config_raw` with
`mem_inv_raw_reachable` and `raw_mem_ok_def` to bound the CURRENT frontier.
`joint_activation_cache_strict` combines this with the existing current
and saved cache bounds, covering zero-size as well as positive sites.
`frame_reachable_mem_inv` and `frame_reachable_saved_mem_inv` expose the
more general transport of any memory invariant to current/saved frames.
No cache-size or initial-zero-frontier premise is needed for these bounds.
Returning restores the caller cache AND frontier
(`return_bind_allocation_frame`); the accepted separation induction
already accounts for this non-monotone current frontier.

### Target strict endpoint: size bridge and actual positions remain

`resolved_token_position`/`resolved_operand_position` give an activation
cache witness and identify `token_positions positions ... tok` with
`positions owner aid`. They do NOT constrain `positions`.
`o1_frame_source_sizes_current` and `_saved` in concretizeAnalysisStageSizes
already give `cache_sizes_ok (source_alloca_sizes owner)` for BOTH kinds
of activation. `cache_sizes_ok_lookup` yields the exact cached size.
`concretize_runtime_context_size` only packages the CURRENT frame case
against imported metadata; it is not a saved-cache canonical bridge.

`canonical_metadata C C' (Allocation aid) p sz` means some source owner has
static items containing `(Allocation aid,sz)` and its output function's
`fn_mems_used` FIND returns `(Allocation aid,p,sz)`.
`concretize_canonical_numeric` proves `p+sz < dimword (:256)` for ALL sizes;
reserved-interval disjointness is only conditional on positive size.
`canonical_metadata_unique` provides position/size uniqueness under global
instruction-ID distinctness. Numeric proof does not need more arithmetic.

Still missing is a CHOSEN position function (not arbitrary positions) and
its cache-to-canonical producer. Its required HOL interface, after choosing
positions from the output owner lookup/FIND, is:

```sml
ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
  (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
callee_first names C.ctx_functions /\ ctx_inst_ids_distinct C /\
o1_run_state_ok vs0 /\
joint_config_reachable vs0 C q /\ activation_cache q depth owner aid (b,sz)
==> canonical_metadata C C' (Allocation aid) (positions owner aid) sz
```

Here `positions` MUST be replaced by the planned actual choice definition,
not universally quantified. This is a missing producer, not a checked
statement. Trace membership of saved owners, static ALLOCA item coverage,
output metadata FIND and cache size equality through existing StageSizes
and MetadataSchedule facts. For memory geometry also prove
`lo <= positions owner aid` from fixed_region_reserved and positive size;
zero-size entries need numeric endpoints, not byte reservation claims.
The current concretizeLayoutRelocation:20-23 assumes this bridge for every
trace cache. That explicit premise remains undischarged.

### Local producer premise ledger

All families need a concrete `local_rel` initialization and invariant
assembly, a chosen Obs (currently abstract), actual instruction/control
alignment, and distinct target taint transport. The following categorizes
the remaining inputs; no family below is unconditional simulation.

* Scalar binary: `guarded_scalar_binary_step` requires operand arity,
  labels equality, every variable operand `clean_scalar`, and Obs stability
  under equal writes. Existing classification/cleanliness interfaces must
  be instantiated at actual reachable uses. Same-tn post equalities do not
  imply an independently tracked target tn is contained.
* Affine: `guarded_pointer_binary_step` requires a resolved pointer tag,
  non-opacity, clean scalar other operand, label equality and Obs stability
  under unequal pointer writes. Modular affine displacement is proved;
  reachable resolution and the combined invariant remain assembly work.
  ADD commutation is available; SUB is pointer-minus-scalar only.
* Comparison: same resolved token/site for both pointers, non-opacity,
  inclusive source-site operand bounds, both strict site endpoints and Obs
  stability. CompareAccess supplies source bounds only; TokenPositions and
  this audit identify endpoint dependencies, not their discharge.
* ASSIGN/parallel PHI: related source lookups, matching predecessor/control,
  and origin/taint update compatibility must be supplied at actual block
  edges. Accepted copy/PHI equations are not reachable control alignment.
* ALLOCA-to-ASSIGN: `local_rel_alloca_assign_step` requires actual target
  literal, cache-hit/fresh split, post pointer/byte predicates for output,
  all other variable predicate transports, `next ==> R` and post Obs.
  Allocation memory is unchanged; fresh taint and lifetime/demand transport
  still need integration. A cache hit's stored size is not the size operand
  without StageSizes. No fresh-memory zero assumption is valid.
* MLOAD: `local_rel_mload_step` requires translated successful address
  evaluations, every unmasked lane in pre-demand R, post output pointer/byte
  predicates, mask empty if P' demands scalar equality, unchanged-variable
  predicate transport, and post Obs. Byte-lane computation is proved;
  actual demand, range endpoint and origin classification are producers.
* MSTORE/MSTORE8: successful address/value evaluations on both sides;
  demanded written bytes lie in both ranges and equal value lanes;
  complement retains R and avoids target write range; post Obs. StoreValues
  supplies demanded lane agreement under trace cleanliness. WriteCoverage
  supplies actual coverage CONDITIONALLY on range translation; the global
  cache-to-layout premise in concretizeLayoutRelocation remains a dependency.
* MCOPY: translated source/destination evaluations and equal length;
  each demanded written pair maps to pre-state copy-source demand;
  retained demand avoids target range; post Obs. Overlap is handled
  simultaneously. CopyTaint transports independent memory taint under the
  same range/complement correspondence, not observations or all components.
* Other memory/observation/control families remain unassembled: ILOAD/
  ISTORE and storage/transient data; memory hashes/logs; RETURN/REVERT;
  external request/outcome/return-copy; branches and terminal results.
  They require equality of clean controls and demanded untainted bytes,
  non-revert exemptions where applicable, observable agreement outside
  source taint/D and explicit post-taint transport. No existing abstract
  Obs premise produces these facts.

Ownership: endpoint/cache metadata/position choice and demanded-write
noncollision depend on source reachability and concretize layout machinery;
operand semantic transport and Obs/taint preservation are local producers;
INVOKE push/pop, terminating fuel adequacy and target-prefix request/final
reflection belong to generic frame/integration work. `taint_within` needs
that reverse reachable/request/final direction even after forward local
simulation is complete. Frozen wrappers must remain blocked until all
these interfaces are instantiated, not merely rebuilt.

### Matched-return semantic boundary (frameInvokeReturn)

`matched_run_invoke_return` now checks the run premise needed by the raw
projection: INVOKE opcode, successful decode/lookup/evaluation/setup,
`run_blocks fuel ctx callee cs = IntRet ret send`, and successful output
binding imply `step_inst fuel ctx callinst caller = OK post`. It additionally
exports restoration of caller vs_allocas and vs_alloca_next. Fuel is EXACTLY
the callee run fuel: no successor or monotonicity assumption is needed.
The run begins at setup_callee's cs, BEFORE entry PHIs (run_defs:1706-1723).
A reachable endpoint alone does not supply that run witness.

### Local-prefix adequacy (frameExecutionPrefix)

`execution_prefix ctx fn entry inst s` now records a finite local execution
from the pre-PHI entry. Its entry/next/block rules retain active endpoints;
next accepts any successful nonterminator step, including a completed
INVOKE, and block accepts a successful nonhalted terminator followed by
`enters_block`. It does not assert termination of unfinished prefixes.

`execution_prefix_return` proves that `wf_function fn`, this prefix and
`step_inst fuel ctx inst s = IntRet ret send` imply an existential-fuel
`run_blocks n ctx fn entry = IntRet ret send`, with exact return and state.
The proof uses a successful `local_return_suffix` from the active instruction
(without repeating entry PHIs), backwards extension and fuel addition.
`prefix_step_fuel_mono` and `prefix_exec_fuel_mono` supply successful-step
and block monotonicity; the corresponding crossBlockSimProofs helpers are
private, while its public `run_blocks_fuel_mono` is reused for calls.

Still required: a parallel activation-prefix stack invariant linked to the
actual decode/lookup/eval/setup witnesses. At return, close the child prefix,
apply `matched_run_invoke_return`, then extend the saved caller prefix.
Neither endpoint reachability nor erased joint-history logs alone supplies
this matched execution invariant or the raw-reachability projection.

### Raw projection from matched activations (frameRawProjection)

`frame_reachable_raw` projects the current activation to `raw_reachable`
under `EVERY wf_function ctx.ctx_functions`; `frame_reachable_saved_raw`
provides the same fact for every saved caller. `joint_config_raw` and
`joint_config_saved_raw` expose these projections for joint endpoints.

The internal matched-prefix stack retains each caller's local prefix and
raw reachability together with the exact decode/lookup/argument/setup
witnesses for its child. On return, `execution_prefix_return` closes the
child from that setup entry, and `matched_run_invoke_return` supplies the
successful caller step. Thus both the saved prefix and raw reachability
advance without adding a return constructor to raw reachability. No
termination of unfinished activations is assumed.
