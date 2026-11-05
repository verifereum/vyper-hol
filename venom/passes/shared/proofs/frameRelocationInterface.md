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

Allocation initialization must be handled separately: joint_writes excludes
ALLOCA fresh-zero initialization. Future untainted read lifetime/birth machinery
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
