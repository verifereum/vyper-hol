# LowerDload semantic boundary audit (.92)

Design artifact, NOT proved HOL declarations. No definition or axiom is
introduced here. In particular the statements below are proposed proof
obligations, not facts available to the integration proof.

## Types and common ambient premises

All displayed formulas are HOL quotations. Free parameters in a displayed
formula are universally quantified, with the following types (the existential
binders shown in formulas override this convention):

```
lo,p,h,N,fuel,sf,j,k : num
P : string -> num set
Sigma : string -> ir_supply
names : string list
C,C' : venom_context
vs0,s,t,t0,u,ss,cs,ct,cs',ct',s1,t1,se,te,s',t' : venom_state
fn,fn' : ir_function
inst,ti,next,rinst : instruction
stk : call_frame list
PG : (num # num) option list
G : (string, num # num) fmap
tn,tnr : taint
A,Ar,Ap : ld_alloc
f,saved,g : ld_frame
fs,fr : ld_frame list
X : instruction list
rs,rt : internal_return
H : (string, ld_site) fmap
nm : string
ops : operand list
args : bytes32 list
```

The notation `B` below is **textual substitution**, never a new HOL constant:

```
B = o1_ctx_shape C /\ o1_run_state_ok vs0 /\
    reserved_intervals_wf C.ctx_global_reserved /\
    fixed_region_reserved lo C /\ ptr_discipline lo C vs0 /\
    fmp_free_ctx C /\
    mem_inv raw_mem_ok C vs0 /\
    mem_inv dload_offset_ok C vs0 /\
    mem_inv dload_headroom_ok C vs0 /\ callee_first names C.ctx_functions /\
    (!fn. MEM fn C.ctx_functions ==>
      lookup_function fn.fn_name C'.ctx_functions =
        SOME (FST (lower_dload_function_supply (Sigma fn.fn_name) fn)))
```

The lookup premise is a stage-derived premise to discharge, NOT an extra
hypothesis proposed for the frozen theorem. Supply freshness/reservation
obligations must also be derived from the stage (configured-origin lemmas);
this audit does not claim lookup equality alone proves supply freshness.
For that reason these are candidate consumer interfaces, not a completeness
claim about B. No hypothesis of source successful execution is part of B.

## 1. Nonterminating expansion exit

Candidate interface at the *last* generated instruction. This version only
handles nonterminating non-INVOKE source instructions; jumps/RET belong to
section 4's separate closures. Retain all correlated witnesses:

```
B /\
ld_sync lo P C vs0 stk PG G tn fn inst s t0 A (f::fs) N /\
ld_global lo A (f::fs) /\
EVERY (\f. f.lf_supply = Sigma f.lf_fn.fn_name) (f::fs) /\
EVERY (\f. !j a. j < LENGTH f.lf_Q /\ EL j f.lf_Q = SOME a ==>
  j IN P f.lf_fn.fn_name) (f::fs) /\
(!j k. j < k /\ k < LENGTH (f::fs) ==>
  list_precedes (EL j (f::fs)).lf_fn.fn_name
                (EL k (f::fs)).lf_fn.fn_name names) /\
fn' = ld_image f /\
ld_envelope f.lf_supply fn s s.vs_inst_idx X p /\
ld_prefix C' fn' X p h t0 t /\ SUC h = LENGTH X /\
~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
step_inst fuel C' (EL h X) t = OK u
==>
?ss Ar g.
  step_inst 0 C inst s = OK ss /\
  u.vs_inst_idx = t.vs_inst_idx /\
  (u with vs_inst_idx := SUC t.vs_inst_idx).vs_inst_idx = p + LENGTH X /\
  g.lf_serial = f.lf_serial /\ g.lf_supply = f.lf_supply /\
  g.lf_fn = f.lf_fn /\ g.lf_Q = f.lf_Q /\
  g.lf_src = (ss with vs_inst_idx := SUC s.vs_inst_idx) /\
  g.lf_tgt = (u with vs_inst_idx := p + LENGTH X) /\
  g.lf_tv = (step_taint inst s ss tn).t_var /\
  step_prov PG G inst ss = ld_erase Ar o_f g.lf_H /\
  ld_vars P Ar g /\ ld_maps Ar g /\
  ld_memory lo Ar (step_taint inst s ss tn) ss u /\
  ld_nonghost (step_taint inst s ss tn) ss u /\
  ld_global lo Ar (g::fs) /\ FDOM Ar = ld_slots Ar (g::fs) /\
  EVERY (ld_maps Ar) fs /\
  (!next. active_inst fn next g.lf_src ==>
    ld_sync lo P C vs0 stk PG (step_prov PG G inst ss)
      (step_taint inst s ss tn) fn next g.lf_src g.lf_tgt Ar (g::fs) N)
```

The explicit pre-location invariant is needed even if there is no next active
instruction. No claim `ld_prefix ... (LENGTH X)` occurs. A future proof must
also preserve ownership, configured supplies and ordering for `(g::fs)`;
fn/Q equality plus unchanged fs already gives those structural predicates.
The conditional ld_sync conclusion is deliberately strong: it carries all
interval, charge, saved-frame and parameter-erasure clauses, rather than
leaving them hidden in an arbitrary postcondition.

Three cases, NOT three new definitions:

* Valid DLOAD `[op] -> [out]`: X has four instructions ALLOCA, ADD,
  CODECOPY, MLOAD. Last h=3; insert the source inst_id in g.lf_E (idempotent
  on repeats). Ar=A: scratch is never a selected original allocation.
  Prove output equality from the *actual copied code bytes*, not from the
  general memory relation applied to private scratch. Update maps, intervals
  and charge, and preserve all old live untainted bytes. Fresh and cached
  scratch both require this proof. Raw safety alone gives none of it.
* Valid DLOADBYTES: X has ADD,CODECOPY; last h=1, g.lf_E=f.lf_E,
  Ar=A. Destination provenance and source taint justify relocated copy
  destinations; generated code source/length must agree. No scratch charged.
* Singleton X=[inst]: h=0,t=t0. Ordinary effects can discharge the value/byte
  clauses conditionally. Original ALLOCA uses its accepted fresh/cached map
  updates; in its fresh case Ar may extend A. Do not reprove that coverage.
  Malformed DLOAD/DLOADBYTES expand as singleton; successful execution must
  first exclude their malformed operand/output shapes by semantic inversion.

`step_inst_non_invoke` removes target and source fuel dependence ONLY after
non-INVOKE has been shown, including every generated instruction. The prefix
uses fuel 0; the supplied final step may use any fuel. `ld_prefix_position`
gives t.vs_inst_idx=p+h; SUC h=LENGTH X gives the post-index equation.

## 2. Successful callee return (no active instruction at returned state)

Here cs,ct are the actual setup states, not arbitrary interior instruction
states. Require entry witnesses `enters_block fn cs s1` and
`enters_block fn' ct t1`; the initial synchronized frame is at s1,t1. Setup
conditions (fresh vars/allocas, first block, prev_bb NONE, inst_idx 0) are to
be supplied by call setup, not inferred from ld_sync. A proposed return
consumer obligation is:

```
B /\
cs.vs_vars = FEMPTY /\ ct.vs_vars = FEMPTY /\
cs.vs_allocas = FEMPTY /\ ct.vs_allocas = FEMPTY /\
cs.vs_inst_idx = 0 /\ ct.vs_inst_idx = 0 /\
cs.vs_prev_bb = NONE /\ ct.vs_prev_bb = NONE /\
fn.fn_blocks <> [] /\ fn' = ld_image f /\
cs.vs_current_bb = (HD fn.fn_blocks).bb_label /\
ct.vs_current_bb = cs.vs_current_bb /\
enters_block fn cs s1 /\ enters_block fn' ct t1 /\
ld_sync lo P C vs0 stk PG G tn fn inst s1 t1 A (f::fs) N /\
ld_global lo A (f::fs) /\
EVERY (\f. f.lf_supply = Sigma f.lf_fn.fn_name) (f::fs) /\
EVERY (\f. !j a. j < LENGTH f.lf_Q /\ EL j f.lf_Q = SOME a ==>
  j IN P f.lf_fn.fn_name) (f::fs) /\
(!j k. j < k /\ k < LENGTH (f::fs) ==>
  list_precedes (EL j (f::fs)).lf_fn.fn_name
                (EL k (f::fs)).lf_fn.fn_name names) /\
run_blocks fuel C' fn' ct = IntRet rt ct'
==>
?sf rs cs' Ar fr tnr rinst se te PG' G' Nr.
  run_blocks sf C fn cs = IntRet rs cs' /\
  ld_sync lo P C vs0 stk PG' G' tnr fn rinst se te Ar fr Nr /\
  TL fr = fs /\ fr <> [] /\
  (HD fr).lf_serial = f.lf_serial /\
  rinst.inst_opcode = RET /\
  step_inst 0 C rinst se = IntRet rs cs' /\
  step_inst 0 C' rinst te = IntRet rt ct' /\
  rs.iret_values = rt.iret_values /\
  rs.iret_adopt_fmp = NONE /\ rt.iret_adopt_fmp = NONE /\
  ld_memory lo Ar tnr cs' ct' /\ ld_nonghost tnr cs' ct' /\
  ld_global lo Ar fr /\ FDOM Ar = ld_slots Ar fr /\
  EVERY (\f. f.lf_supply = Sigma f.lf_fn.fn_name) fr /\
  EVERY (\f. !j a. j < LENGTH f.lf_Q /\ EL j f.lf_Q = SOME a ==>
    j IN P f.lf_fn.fn_name) fr /\
  (!g. MEM g fs ==>
    FRANGE g.lf_H SUBSET ld_slots Ar fs /\
    (!a. MEM (SOME a) g.lf_Q ==> a IN ld_slots Ar fs)) /\
  (!k. k IN FDOM A /\ k IN ld_slots A fs ==>
    FLOOKUP Ar k = FLOOKUP A k) /\
  (!k. k IN ld_slots Ar fs ==>
    FLOOKUP (DRESTRICT Ar (ld_slots Ar fs)) k = FLOOKUP Ar k)
```

PG',G' are explicitly existential with the same ghost types as PG,G;
Nr:num. `ld_sync` is used at se,te BEFORE RET, never at
cs',ct'. In particular it supplies terminal `frame_reachable` with the same
saved stack stk, not merely whole-run equality. RET leaves the state intact;
no opaque return token is compared. The returned vector is FRONT of evaluated
RET operands. `fn_ptr_ok` excludes pointer returns and RETFMP/DRET; taint_ok
excludes tainted returned values. These exclusions must be used to prove
scalar vector equality and NONE adoption, not assumed for arbitrary programs.

Ap = DRESTRICT Ar (ld_slots Ar fs) is the surviving map. `ld_memory_restrict`
gives memory for Ap. `ld_erase_restrict_compose` preserves each saved source
G, and `ld_wordrel_restrict` preserves each saved selected parameter. The
FRANGE/Q obligations above are precisely their side conditions. The domain
and saved-map clauses are needed even with zero-size allocations: numerical
(base,size) inverse lookup is not a valid substitute for identity.

The terminal ghost state tnr contributes t_mem/t_stor/t_trans/t_imm. On pop,
variable taint is replaced by saved cf_tvar restricted away from outputs.
Do NOT restore the old saved memory taint. ld_nonghost must be re-established
for the merged caller: its call-entry FMP/context fields come from the saved
caller, not the returned callee.

## 3. Exact INVOKE consumer and restoration

The elementary semantic consumer is fully typed by the conventions above:

```
inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm,ops) /\
lookup_function nm C.ctx_functions = SOME fn /\
eval_operands ops s = SOME args /\ setup_callee fn args s = SOME cs /\
run_blocks sf C fn cs = IntRet rs cs' /\
bind_outputs inst.inst_outputs rs.iret_values
  (adopt_return_fmp rs (merge_callee_state s cs')) = SOME s'
==> step_inst sf C inst s = OK s'
```

Derivation: rewrite `step_inst_def` once, rewrite the opcode/decode/lookup/
eval/setup/run/bind equations. There is no equating sf with target fuel.
`ld_invoke_success` is the checked inverse direction on the TARGET; it does
not construct the source run. Source bind success follows from target bind
success, equal return vector and equal output list (length test in
bind_outputs_def). Its resulting s' is the source witness, not the target t'.

For stk=(cf::rest), terminal frame_reachable from section 2 plus source RET
step and source bind gives `frame_reachable_ret`, with post ghosts

```
DRESTRICT cf.cf_prov (COMPL (set cf.cf_inst.inst_outputs))
tnr with t_var := DRESTRICT cf.cf_tvar
                    (COMPL (set cf.cf_inst.inst_outputs))
```

and state `s' with vs_inst_idx := SUC cf.cf_state.vs_inst_idx`.
The restored target index is the saved target index plus one (INVOKE is a
singleton). Restore saved.lf_Q unchanged, restrict saved.lf_H away from
outputs, keep saved serial/supply/fn/E. Pop to `(restored::TL fs)` when
fs=(saved::TL fs). `ld_ownership_pop` supplies only the Q permission formula;
it supplies NO map, memory, interval, or sync theorem. `merge_callee_state`
restores caller vars/params/allocas/frontier/control and propagates memory,
transient,accounts,returndata,logs,outcomes,requests,pending deletions,
immutables. Historical logs/requests need not agree. Return NONE adoption
preserves caller FMP. Future caller variable taint and H must clear outputs,
matching the precise frame_reachable_ret rule above.

## 4. Seven closure matrix for ld_successful_run_induction

| Closure (source lines in RunInduction) | Checked boundary usable now | Missing concrete closure |
|---|---|---|
| base non-INVOKE (22-25) | step_inst_non_invoke; ordinary value/write effects; original ALLOCA effects/coverage | Section 1 DLOAD/DLOADBYTES completion; terminal RET value equality; jumps need control observations. Prefix interior is a stutter, not a source step. |
| INVOKE (26-34) | ld_invoke_success; ld_ownership_push_saved; ld_arguments_permission | Entry paired setup + nested R instantiated with section 2, then section 3 merge/bind/pop. R is available for the nested callee in this premise; caller raw IH is not its replacement. |
| nonterminal next (35-42) | ld_prefix_position, ld_prefix_extend; ld_sync_ordinary_witness and ld_sync_ordinary_owned_coverage | Interior prefix extends without advancing source; last step consumes section 1, then uses suffix E. Need source block continuation with existential fuel. |
| terminator OK (43-47) | source frame_reachable_block rule after enters_block | Concrete branch/control agreement and block-exit postcondition; cannot use section 1's nonterminator interface. |
| block IntRet (48-51) | frame_reachable_ret is a later caller consumer, not this closure | RET base result + reachable terminal witness must pass unchanged through E. |
| run block OK then recurse (52-59) | existing phi effects/entry/locations | Establish paired enters_block/phi ghosts, lift E result to next R with source fuel increment; retain terminal witness from recursive R. |
| run block IntRet (60-65) | ld_successful_run_induction itself is checked | Same entry/phi lift; propagate E terminal witness and construct run_blocks (SUC sf) source equation. |

No existing lemma proves section 2. Generic semantic induction proves that
these seven closures suffice, not that they hold. Ordinary coverage lemmas
have explicit effect premises and are not unconditional step simulations.
No DLOAD expansion effect theorem was found beyond scratch raw-prefix safety:
`lower_dload_supply_prefix_raw` and `lower_dload_expansion_prefix_raw` do not
supply source completion, returned outputs, ghost maps or memory agreement.

## Review request: at most three durable semantic groups

1. Expansion completion (section 1), including fresh/cached scratch and copy
   byte effects, reusing existing original-ALLOCA proofs unchanged.
2. Concrete mutual semantic simulation using the seven checked closures,
   with explicit prelocation/block-exit/terminal packages. Include setup,
   RET, jump, phi and merge/pop here, NOT more ordinary-opcode adapters.
3. Target raw-reachability coverage and frozen theorem integration, consuming
   the return-producing simulation for atomic INVOKE.

Dependency is 1 -> 2 -> 3. No use of raw coverage to prove 2 is allowed;
source frame_reachable comes from the synchronized entry witness and its
own next/block/call/ret rules. Exact closure predicates for E/S (not merely
R) and sufficiency of configured freshness premises still require strategist
review before authorizing proofs. This audit deliberately makes those gaps
visible instead of calling the architecture de-risked.

## 6. Endpoint audit (.12.2): producer matrix and consumer experiment

This section is an audit, not a claim of endpoint assembly. The exact
`ld_sync_def` inspected is SafetyRelation lines 123–153. The baseline
ExpansionGhost target builds. The temporary identity consumer was removed to
avoid retaining a near-duplicate effect lemma.

### Ambient correction

In B above, `callee_first names C` must read
`callee_first names C.ctx_functions`. Add the stage-derived clause
`!fn. MEM fn C.ctx_functions ==> ir_supply_covers_fn (Sigma fn.fn_name) fn`.
Neither correction is a new assumption for the frozen theorem. Do not use B
as an actual checked HOL predicate before making these textual corrections.

### Section 1 conclusion coverage

| Required field | Existing interface and exact restriction | Remaining obligation |
|---|---|---|
| actual source success | `ld_sync_identity_effect`, `ld_sync_assignment_effect`, `ld_sync_arithmetic_effect`, `ld_sync_param_effect`, `ld_sync_observational_read_effect`, `ld_sync_classified_read_effect`, storage/immutable/write and oracle effects | These are same-instruction effects, not DLOADBYTES expansion effects. `ld_dload_expansion_ghost_exit` supplies DLOAD success on its correlated trace. No source-success assumption may replace an actual producer. |
| target unchanged instruction index | oracle and memory-write effects export it explicitly; `ld_prefix_position` gives the incoming `p+h` | Other effect signatures do not all export it: use nonterminating semantic index preservation, not target activity. |
| post index p+LENGTH X | `ld_prefix_position` and SUC h=LENGTH X | arithmetic only, after the unchanged-index equation |
| serial/supply/fn/Q | record update preserving these fields | g must be chosen once, shared with H/E/map witnesses |
| src/tgt/tv equations | record constructor; producer gives tn'=step_taint | no location assumption needed |
| step_prov erasure, ld_vars, selected H support | ordinary effects export these for unchanged A; ghost exit for DLOAD | transfer vars through final index updates; DLOADBYTES ghost noninterference and fresh-ALLOCA map change must be correlated |
| ld_maps g | incoming maps + unchanged allocations/frontiers/E for ordinary effects | DLOAD changes E/frontier; fresh original ALLOCA changes A. Use their actual map updates, not ordinary_advance. |
| ld_memory, ld_nonghost | ordinary effects export both at unincremented ss,ts | DLOAD ghost exit is not memory preservation. Private CODECOPY theorem requires owned-private destination; DLOADBYTES writes a potentially public selected destination and is not private. |
| ld_global, FDOM/slots, EVERY saved maps | ordinary unchanged-site congruence; original fresh allocation proof has the necessary erasure/saved-map reasoning | Existing `ld_sync_head_update` and `ld_sync_fresh_alloca_update` conclude these only jointly with an active-next sync. Factor the location-independent result once, not per opcode. |
| conditional final ld_sync | `ld_sync_ordinary_advance` given source next activity AND next envelope; original allocation advances similarly | Need source-active-successor envelope transport. `ld_envelope_singleton_next` instead assumes active target successor, so does not discharge the required implication. |

Additional effect premises are real obligations. Observational reads additionally
ask EVERY(fn_ptr_ok P), already supplied by incoming sync. Classified reads
ask headroom and, for MLOAD/ILOAD, `~in_revert_forward fn s`. Oracle CALL and
STATICCALL also ask headroom and non-forwarding. The memory-write producer
covers only MSTORE/MSTORE8/MCOPY and asks fn_shape_ok, fn_inst_wf, labels,
non-forwarding, and target frontier < dimword. Source shape, labels and
pointer/access/taint facts have existing sync/ambient projections; none of
these signatures covers DLOADBYTES merely because it writes memory.

`ld_sync_alloca_owned_coverage` (AllocationCoverage 63–100) asks source next
activity, a next envelope, and target next activity. The fresh and cached
advance theorems therefore cannot be used backwards to obtain unconditional
post-fields. `ld_sync_fresh_alloca_update` (Allocation 485–506) explicitly
assumes reachable/active next and next envelope; its proof already contains
saved-frame erasure, maps/vars and interval reasoning. Reuse/generalize that
implementation instead of duplicating it.

### Every ld_sync clause, independent of whether next exists

| Definition lines | Preservation obligation |
|---|---|
| 125–126 nonempty/head fn/src/tgt/tv | constructor equations |
| 127 reachable/active | `frame_reachable_next` needs incoming reachable, actual source success, nonterminator and active source successor; it is used only inside the final implication |
| 128 EVERY fn_ptr_ok; 129 stack length | unchanged C, stk, tail |
| 130 G erasure | effect's step_prov equation (fresh map erasure for original allocation) |
| 131 PG erasure of Q | unchanged Q and A for ordinary/DLOAD/BYTES; fresh-map erasure preservation for ALLOCA |
| 132 serial distinct | unchanged serial/tail |
| 133 serial bound/maps/vars | serial unchanged; effect vars; maps requires actual allocation/E update |
| 134 intervals | unchanged frontier for ordinary; allocation preservation theorem for allocating cases |
| 135–137 prev/current block, membership | effect control equalities, incoming control equality, fn unchanged |
| 138 domain/slots | unchanged-site congruence or original fresh extension; never inverse address identity |
| 139–141 per-frame frontier/charge | ordinary unchanged; scratch ownership fresh/cached charge; original ALLOCA equal size increment |
| 142–145 per-frame envelope | saved frames unchanged; head needs NEW envelope from source next activity, not target-successor assumption |
| 146–151 saved caller fn/state/G/PG/tvar | unchanged tail; if A extends, saved erasure equations required |
| 152 total charge bound | ordinary/original ALLOCA unchanged E; DLOAD requires idempotent fresh/cached charge proof |
| 153 memory/nonghost | actual semantic effect, then index-insensitivity |

### DLOADBYTES semantic trace (not yet a paired write theorem)

Defs 161–173 expands *every* three-operand DLOADBYTES, regardless of outputs,
into ADD `[src; Label "code_end"]` followed by CODECOPY
`[dst; Var fresh; size]`. Malformed operand length is singleton.
Semantics 969–980 ignores outputs and requires three evaluable operands;
CODECOPY 983–994 likewise ignores outputs. Thus it is incorrect to exclude a
DLOADBYTES merely because outputs are nonempty. Source shape/wf may exclude
that separately. DLOAD uses exec_read1, so its successful output/operand shape
must be inverted through exec_read1 rather than inferred from the pass.

Write bytes are exactly
`TAKE (w2n size) (DROP (w2n src) s.vs_data_section ++ REPLICATE (w2n size) 0w)`;
target uses the analogous DROP from code at evaluated `src + code_end`.
A paired proof needs data/code suffix equality, scalar src and size equality,
correct label evaluation and the dload_offset_ok no-word-wrap bound. Fresh
ADD output must not change evaluation of original dst/size. Destination
classification comes from access_ok and selected provenance; only nonempty
writes need interval containment and target no-wrap (headroom). For size=0,
TAKE 0 gives []; no address-provenance containment should be demanded, but
memory expansion/metadata behavior still follows the actual write function,
not an assumed no-op. The current generic write effect excludes this opcode;
private CODECOPY cannot substitute for selected/public relocated overwrite.
A new actual paired DLOADBYTES byte/write effect remains necessary.

### Exact common nonallocating reconstruction statement (checked)

This nonallocating version is exported as `ld_nonallocating_endpoint` in
`lowerDloadSafetyAdvanceTheory`. Its allocation/ownership reasoning is factored
through `ld_head_allocation_update`, also reused by `ld_sync_head_update`.
The corresponding allocation/scratch versions must change A/E and preserve
the same fields.

```sml
ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
ld_global lo A (f::fs) /\ o1_ctx_shape C /\
~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
ld_envelope f.lf_supply fn s s.vs_inst_idx [inst] p /\
t.vs_inst_idx = p /\
step_inst 0 C inst s = OK ss /\ step_inst 0 C' inst t = OK ts /\
tn' = step_taint inst s ss tn /\ G' = step_prov PG G inst ss /\
g = f with <|lf_src := ss with vs_inst_idx := SUC s.vs_inst_idx;
              lf_tgt := ts with vs_inst_idx := SUC p;
              lf_H := H'; lf_tv := tn'.t_var|> /\
ld_vars P A (f with <|lf_src := ss; lf_tgt := ts;
                      lf_H := H'; lf_tv := tn'.t_var|>) /\
ld_memory lo A tn' ss ts /\ ld_nonghost tn' ss ts /\
G' = ld_erase A o_f H' /\
(!a. a IN FRANGE H' ==> a IN FDOM A) /\
ss.vs_allocas = s.vs_allocas /\ ts.vs_allocas = t.vs_allocas /\
ss.vs_alloca_next = s.vs_alloca_next /\
ts.vs_alloca_next = t.vs_alloca_next /\
ss.vs_current_bb = s.vs_current_bb /\ ts.vs_current_bb = t.vs_current_bb /\
ss.vs_prev_bb = s.vs_prev_bb /\ ts.vs_prev_bb = t.vs_prev_bb
==>
ld_vars P A g /\ ld_maps A g /\
ld_global lo A (g::fs) /\ FDOM A = ld_slots A (g::fs) /\
EVERY (ld_maps A) fs /\
(!next. active_inst fn next g.lf_src ==>
  ld_sync lo P C vs0 stk PG G' tn' fn next g.lf_src g.lf_tgt A (g::fs) N)
```

No target successor is a premise. The two actual successes are appropriate
premises ONLY for this common post-effect constructor; the enclosing endpoint
must produce source success from target success before applying it.

### Checked consumer and exact obstruction

Temporary local `ld_identity_endpoint_audit` applied `ld_sync_identity_effect`
and obtained actual source success, vars, memory, nonghost, provenance and
allocation equations without either successor premise. Its reduced consumer
built with `null(hyp ld_identity_endpoint_audit)` checked (tool output
TO_ld_mem-20261104T190123Z_m6842_t001). It was removed to avoid duplication.
The full consumer, requiring only source activity inside its final implication,
reached the conditional sync residual with all effect fields in context
(TO_ld_mem-20261104T190123Z_m6827_t001). Attempting existing ordinary_advance
exposed its next-envelope requirement and unfixed frame/effect witnesses
(TO_ld_mem-20261104T190123Z_m6838_t001). No further tactic chain was pursued.
This does NOT prove that the common constructor above exists. Missing
infrastructure: source-active envelope transport, location-independent
maps/global/saved-map/charge reconstruction, and DLOADBYTES actual write
transport. The audit is ready for a scoped strategist checkpoint, not broad
endpoint assembly.

### Common nonallocating constructor validation

`ld_nonallocating_endpoint` now proves the exact statement above, with
unconditional vars/maps/global/domain/saved-map fields and only the last sync
clause conditional on source activity. It uses `ld_envelope_source_next` and
`frame_reachable_next` inside that implication. A temporary full identity
consumer combined `ld_sync_identity_effect` with this constructor, producing
actual source success and all fields without target successor activity. It
built with `null(hyp ld_identity_endpoint_audit)` checked
(TO_ld_mem-20261104T190123Z_m6941_t001), then was removed to avoid duplication.
The producer-to-constructor application used forward `drule_all` after
instantiating only the two ghost equations tn'/G'; no source/effect witnesses
were recovered by backwards application. The permanent three boundaries also
have explicit `null(hyp ...)` assertions. Public DLOADBYTES writes and changing
allocation/scratch endpoint reconstruction remain separate obligations.

## 7. Public DLOADBYTES probe (.12.6)

### Checked payload and reduced overwrite consumer

`ld_dloadbytes_codecopy_payload` in CodeDataBytes now produces actual source
`step_inst_base inst s = OK ss`, together with ONE shared byte list and both
source/target `write_memory_with_expansion` equations. It assumes independently
evaluated source dst/off/len and target dst'/(off+basew)/len, code equality,
code_layout_valid and the explicit no-wrap bound. Its statement permits every
length, including zero, and does not restrict outputs. The kernel hypothesis
list is explicitly checked empty. This is not yet a trace-to-effect theorem.

A temporary `ld_public_payload_audit` checked the following reduced consumer:

```
ld_memory lo A tn s t /\ LENGTH bytes = n /\
(n = 0 \/
 (FLOOKUP A k = SOME (b,c,sz) /\ d = b+delta /\ d' = c+delta /\
  delta+n <= sz /\
  (!a u v z. FLOOKUP A a = SOME (u,v,z) ==> lo <= u /\ lo <= v) /\
  (!a u v z. FLOOKUP A a = SOME (u,v,z) /\ a <> k /\ 0 < z /\ 0 < sz ==>
    (u+z <= b \/ b+sz <= u) /\ (v+z <= c \/ c+sz <= v)))) /\
tn'.t_mem = tn.t_mem DIFF {d+j | j < n}
==>
ld_memory lo A tn'
  (write_memory_with_expansion d bytes s)
  (write_memory_with_expansion d' bytes t)
```

The zero case used `ld_empty_write_read_byte`, not state equality or selected
containment. The selected case used `ld_memory_write_slot` with M={} and the
same byte list on both sides. The audit built with an empty hypothesis list
(TO_ld_mem-20261104T190123Z_m6986_t001). It and its temporary ancestors were
removed to avoid retaining a duplicate specialization. Low destinations use
`ld_memory_write_low` with M={} instead; no new overwrite theorem is needed.
Restored CodeDataBytes builds (TO_ld_mem-20261104T190123Z_m6995_t001).

### Required correlated effect interface (UNPROVED)

With the section 1 ambient/sync/ownership inputs, let the actual expansion be
`X=[ADD [r;Label "code_end"] [z]; CODECOPY [d;Var z;n] []]` with its actual
supply-generated ids, incoming target index p, prefix at h=1, and successful
final target step `step_inst 0 C' (EL 1 X) t1 = OK u`. The producer must yield
ONE tuple `ss,H',G',tn'` such that:

```
step_inst 0 C inst s = OK ss /\
tn' = step_taint inst s ss tn /\ G' = step_prov PG G inst ss /\
G' = ld_erase A o_f H' /\
(!a. a IN FRANGE H' ==> a IN FDOM A) /\
ld_vars P A (f with <|lf_src := ss; lf_tgt := u;
                     lf_H := H'; lf_tv := tn'.t_var|>) /\
ld_memory lo A tn' ss u /\ ld_nonghost tn' ss u /\
ss.vs_allocas = s.vs_allocas /\ u.vs_allocas = t0.vs_allocas /\
ss.vs_alloca_next = s.vs_alloca_next /\
u.vs_alloca_next = t0.vs_alloca_next /\
ss.vs_inst_idx = s.vs_inst_idx /\ u.vs_inst_idx = p+1 /\
ss.vs_current_bb = s.vs_current_bb /\ ss.vs_prev_bb = s.vs_prev_bb /\
u.vs_current_bb = t0.vs_current_bb /\ u.vs_prev_bb = t0.vs_prev_bb
```

This feeds a generalized nonallocating endpoint constructor using the actual
expansion, not the singleton version's same-instruction premises. The final
increment changes u's index to p+2. No successor activity is required for the
effect fields. Source activity is used only for successor sync.

### Exact residual boundaries for planning

1. **Trace evaluations/fresh ADD:** derive source off/len evaluations and
   target matching scalar evaluations from sync, source taint/access facts and
   original-operand membership. Invert the one ADD prefix to obtain
   `eval_operand (Var z) t1 = SOME (off+basew)` and preserve evaluations of d/n
   and original-variable observations. Supply coverage must give
   `~MEM z (fn_ir_vars fn)` and `d <> Var z`, `n <> Var z`. Label evaluation,
   code equality and the no-wrap bound must be projected from nonghost,
   code_layout_valid and dload_offset_ok, not added as frozen assumptions.
2. **Address classification:** for nonzero len, produce either equal low
   destinations with `dst+len<=lo`, or ONE selected identity k, equal delta,
   source/target bases and `delta+len<=sz` plus global bounds/separation.
   These are exactly the existing low/slot overwrite consumer premises. For
   zero length skip this classification completely.
3. **Ghost/taint update:** derive the displayed t_mem difference (empty
   payload mask) from actual source step_taint. Derive H'/G' and t_var update
   from actual source outputs; DLOADBYTES semantics ignoring outputs does NOT
   justify silently assuming them empty. If fn_inst_wf supplies empty outputs,
   project that fact before choosing H'=f.lf_H and unchanged variable taint.
   Otherwise account for the actual set_prov/set_var_taint updates.
4. **Remaining effect fields:** combine source/target write equations with
   expansion-only fresh-variable observations using ld_vars_observation_cong;
   prove nonghost under the new taint and actual public writes, not by private
   CODECOPY noninterference. Allocation/control/index equations follow the
   actual ADD and copy semantics and prefix position. None has yet been
   packaged with the produced ss/H'/G'/tn' witnesses.

The payload and reduced selected/zero consumer are checked; the four items
above are precise remaining integration obligations, not claimed proofs.

## 8. Allocation/scratch location-independent diagnostic (.12.7)

### Checked reduced consumer

A temporary `ld_scratch_endpoint_audit` in ScratchOwnership consumed the actual
`exec_alloca inst f.lf_tgt 32w = OK u` and the exact premises of
`ld_scratch_alloca_ownership` (covered supply, distinct original ids, private
site d/ai, maps/global/intervals, source absence, frontier lower bounds and
stack frontier/charge equations). It selected
`g=f with <|lf_tgt:=u; lf_E:=d INSERT f.lf_E|>` and obtained the actual fresh OR
cached ownership outputs. It then transferred them to

```
h = f with <|lf_src := ss; lf_tgt := ts;
             lf_E := d INSERT f.lf_E; lf_H := H'; lf_tv := tv'|>
```

under ONLY these additional structural premises:

```
ss.vs_allocas = f.lf_src.vs_allocas /\
ss.vs_alloca_next = f.lf_src.vs_alloca_next /\
ts.vs_allocas = u.vs_allocas /\ ts.vs_alloca_next = u.vs_alloca_next /\
(!k. k IN FRANGE H' ==> k IN FDOM A)
```

The checked conclusion was

```
ld_maps A h /\ ld_global lo A (h::fs) /\
ld_slots A (h::fs) = ld_slots A (f::fs) /\
ld_charge (h::fs) = ld_charge (f::fs) + (if d IN f.lf_E then 0 else 1) /\
ts.vs_alloca_next = f.lf_tgt.vs_alloca_next +
  32 * (if d IN f.lf_E then 0 else 1)
```

Transfer used the existing `ld_head_allocation_update` at g, not at the incoming
f (their target allocation maps differ!). The experiment built and explicitly
checked `null(hyp ld_scratch_endpoint_audit)`
(TO_ld_mem-20261104T190123Z_m7018_t001). It was removed rather than retained as a
near-duplicate adapter; restored ScratchOwnership and ExpansionGhost build
(TO_ld_mem-20261104T190123Z_m7025_t001). This is a reduced structural consumer,
not a proof that the entire expansion has those additional premises.

### Minimal common location-independent output package (not a definition)

For actual final source/target states sn/tt and a single correlated g,A',H',tn',
the structural portion needed before any successor split is:

```
ld_maps A' g /\ ld_global lo A' (g::fs) /\
FDOM A' = ld_slots A' (g::fs) /\
EVERY (\h. ld_maps A' h /\ ld_vars P A' h) fs /\
EVERY (\h. ld_erase A' o_f h.lf_H = ld_erase A o_f h.lf_H /\
  MAP (OPTION_MAP (ld_erase A')) h.lf_Q =
  MAP (OPTION_MAP (ld_erase A)) h.lf_Q) (f::fs) /\
ld_intervals lo sn /\ ld_intervals lo tt /\
(!j. j < LENGTH (g::fs) ==>
  (EL j (g::fs)).lf_tgt.vs_alloca_next =
  (EL j (g::fs)).lf_src.vs_alloca_next + 32 * ld_charge (DROP j (g::fs))) /\
ld_charge (g::fs) <= ctx_dload_count C
```

Together retain g's serial/fn/supply/Q equations, its actual H'/tv' and sn/tt,
source/target block-control agreement, PG erasure for g.Q, and unchanged saved
caller clauses/envelopes. Head vars, memory, nonghost and G' erasure are actual
effect outputs, not structural assumptions to be smuggled into a final
trace-to-effect theorem. Reachability and the new head envelope enter only the
source-active-successor implication. This package is deliberately textual;
no new predicate or definition is proposed.

### Changed-map/E audit against existing implementations

| Case | A'/E'/slots and saved erasures | Existing producer / exact residual |
|---|---|---|
| cached original ALLOCA | A'=A, E'=E, slots unchanged; all saved erasures reflexive; charge unchanged | `ld_cached_alloca_effect` gives actual ss and paired value/byte/ghost effects with no successor premise. Its explicit update_var equations meet `ld_head_allocation_update`. The current advance wrapper unnecessarily requires source successor/envelope; do not use it to obtain unconditional fields. |
| fresh original ALLOCA | A'=A extended at (serial,inst_id), E'=E; slots insert this key; saved erasures from `ld_global_fresh_erasures`; tail maps/vars from `ld_frames_fresh_update` | `ld_fresh_alloca_dispatch` and `ld_fresh_alloca_effect` supply actual success/effects; `ld_sync_original_site_fresh` derives target/key freshness and not-private from covered sync. Structural proof is already in `ld_sync_fresh_alloca_update` lines 509–568 and must be FACTORED there, not copied. Its current statement hides all unconditional fields behind source reachable/active/envelope premises. |
| fresh DLOAD scratch | A'=A, E'=d INSERT E, slots unchanged; saved erasures reflexive | `ld_scratch_alloca_ownership` gives actual private allocation, global/maps/intervals and charge/frontier equations. Reduced consumer above transports them to final states with the exact allocation/frontier equalities. Still need actual trace derivation of those equalities, final intervals and support. |
| cached DLOAD scratch | A'=A, E'=E because d already in E; slots unchanged; saved erasures reflexive | SAME ownership theorem and reduced consumer. Its `ld_private_cache` use proves cache membership iff executed identity. No second charge is added. |

Fresh original insertion also handles size zero: domains/slots still change,
though frontiers do not. Do not replace the insert equation by unchanged maps
on the basis of zero size. Global support for a changed H' is discharged from
the actual effect's FRANGE inclusion. Serial distinctness and saved stack
length/order persist because no push/pop occurs.

### Ghost compatibility and exact remaining DLOAD obligations

`ld_dload_expansion_ghost_exit` supplies actual source success, vars for
`H'=set_prov f.lf_H [out] NONE`, tn'=step_taint, nonghost and G' erasure, plus
source unchanged allocations/frontier and final target index p+3. It does NOT
supply target allocation/frontier equations relative to u (the scratch ALLOCA
result), ld_memory, global ownership, selected support or the charge bound.
The reduced consumer above therefore tests the structural side required by
that ghost result without claiming their full correlated composition is
already checked. Its chosen H'/tv' are compatible in shape; derive support
from incoming global selected support and the actual set_prov deletion.

Remaining exact obligations for assembly:

* Trace preservation from u through ADD/CODECOPY/MLOAD: target allocas/frontier
  unchanged, source final allocas/frontier unchanged. Transfer intervals and
  stack frontier equations through those same states, never through arbitrary
  unrelated witnesses. Scratch ownership already proves the fresh/cached
  increment; the final `ld_charge(g::fs)<=ctx_dload_count C` still needs the active-stack count
  budget and d belonging to the configured original DLOAD ids.
* Private CODECOPY preservation of old live bytes: derive lo<=scratch base,
  every target original site disjoint from [scratch,scratch+32), including
  caller sites, from the post-allocation global/private ownership. Use
  `ld_memory_write_private` for the actual shared payload, not `ld_memory`
  alone to infer scratch contents. ALLOCA itself does not initialize bytes.
* The actual scratch bytes read by MLOAD use `ld_codecopy_source_mload` plus
  ADD evaluation, labels/code-layout and no-wrap. This is a distinct fact
  from private noninterference; both are needed. Preserve it through the
  actual intermediate states before final MLOAD success/ghost construction.
* Relate source DLOAD taint to incoming memory taint (DLOAD is a read, not a
  public memory write), transport ld_memory to the paired final states,
  and combine with the SINGLE source ss already produced by ghost exit.
* Generalize/factor fresh original structural reconstruction once, then use
  source-forward envelope progression and actual source success for final
  conditional sync. No target successor activity is available or required.

No unconditional allocation fields were inferred from the conditional fresh
advance theorem, and no saved-map erasure proof was duplicated. These are the
remaining producer/factoring obligations for strategist review, not a completed
allocation endpoint theorem.

## Current singleton dispatch audit (.16, in progress)

E0249 supersedes earlier claims that the actual four-instruction DLOAD
endpoint is missing: `ld_dload_endpoint` and `ld_dloadbytes_endpoint` are
exported in ExpansionEndpoint with empty kernel hypotheses. This does not
close singleton dispatch. The following inventory is source inspection,
not a claim that a dispatcher has been checked.

The common P is not a gap: `ld_sync_def` explicitly includes
`EVERY (fn_ptr_ok P) C.ctx_functions` (line 128). Arithmetic and assignment
producers therefore do not need a different existential pointer policy.

Inspected unconditional producers (all take successful target steps, not
successful source steps or successor activity):

* `ld_sync_arithmetic_effect`: MUL, Div, Mod, SDIV, SMOD, Exp, ADDMOD,
  MULMOD, SLT, SGT, ISZERO, AND, OR, XOR, NOT, SIGNEXTEND, BYTE, OFFSET,
  ADD, SUB, SHL, SHR, SAR.
* `ld_sync_assignment_effect`: ASSIGN, RETPC_PARAM. Current opaque-return
  policy must be retained; no return-token equality is required here.
* `ld_sync_observational_read_effect`: CALLER, ADDRESS, CALLVALUE, GAS,
  ORIGIN, GASPRICE, CHAINID, COINBASE, TIMESTAMP, NUMBER, PREVRANDAO,
  GASLIMIT, BASEFEE, BLOBBASEFEE, CALLDATASIZE, RETURNDATASIZE, CODESIZE,
  BLOCKHASH, BLOBHASH, CALLDATALOAD, BALANCE, SELFBALANCE, EXTCODESIZE,
  EXTCODEHASH, SLOAD, TLOAD.
* `ld_sync_classified_read_effect`: MLOAD, ILOAD, LT, GT, EQ; additionally
  requires source non-revert for memory reads and source headroom invariant.
* `ld_sync_param_effect`: PARAM; requires the stack-wide selected-Q
  permission already present in the endpoint ambient premises.
* `ld_sync_memory_write_effect`: MSTORE, MSTORE8, MCOPY; requires projected
  shape, labels, non-revert, and target frontier below dimword.
* `ld_sync_istore_effect`: ISTORE; same additional projections as writes.
* `ld_sync_oracle_call_effect`: CALL, STATICCALL; non-revert and source
  headroom invariant suffice with common sync/global/shape/discipline.

The arithmetic, assignment, observational and classified-read producers
export correlated ss,H', provenance support, memory/nonghost, unchanged
allocation maps/frontiers and current/previous block fields. PARAM has the
same output. Write producers preserve H and additionally export indices;
oracle-call output also exports indices. Their assumptions listed above
are not yet a checked final dispatcher application.

Original ALLOCA cannot use the successor-conditioned owned-coverage theorem
for unconditional success. `ld_fresh_alloca_structure` is unconditional,
but consumes paired exec_alloca success, fresh source/target entries and A
key, no private-id collision, correlated value/memory/nonghost effects,
frontier lower bounds and H' support. It produces post maps/global/slots,
suffix maps/vars and erasure preservation, intervals and charge/frontier
facts. These inputs still need to be composed with fresh/cached effect
producers in the actual singleton dispatcher.

Classification pitfalls checked against current definitions:
`fmp_free_ctx` excludes DALLOCA,DRET,GETFMP,SETFMP,RETFMP through
`is_raw_fmp_opcode`; it does NOT itself exclude INITIAL_FMP,BUMP,FMP_PARAM,
MEMTOP. `raw_opcode_ok` excludes all these plus PHI and ASSERT_UNREACHABLE;
its availability must be obtained from the actual source shape contract.
`is_terminator` excludes JMP,JNZ,DJMP,RET,RETURN,REVERT,STOP,SINK,
SELFDESTRUCT,INVALID,DRET,RETFMP from this nonterminating interface.
INVOKE is separately excluded. PHI step semantics returns Error outside
the phi prefix, independently of whether raw shape excludes it.

Still to finish in this audit: inspect storage/identity producer fields;
classify CODECOPY,CALLDATACOPY,RETURNDATACOPY,EXTCODECOPY,SHA3,LOG,
DELEGATECALL,CREATE,CREATE2 and malformed DLOAD/DLOADBYTES; verify raw-shape
projections and original cached/fresh ALLOCA inputs; run and remove the
checked arithmetic/assignment endpoint consumer experiment. No residual
in this paragraph is asserted impossible merely from its opcode name.

Additional inspected common-output producers:
`ld_sync_storage_write_effect` covers SSTORE,TSTORE and
`ld_sync_identity_effect` covers NOP,ASSERT,ASSERT_UNREACHABLE. Both have
exactly the same unconditional ss,H' support/memory/allocation/control
output shape as arithmetic, under sync/global/o1_ctx_shape/ptr_discipline
and target OK. Thus ASSERT_UNREACHABLE need not be excluded for this
producer even if a stronger raw source contract also excludes it.

Important correction from inspecting o1PassContract lines 340–358:
`o1_ctx_shape`/`o1_fn_shape` do NOT contain `raw_opcode_ok`. Consequently
INITIAL_FMP,BUMP,FMP_PARAM,MEMTOP cannot be discarded using that absent
premise. This is a genuine residual classification obligation, not an
invitation to strengthen ambient assumptions. DALLOCA/GETFMP/SETFMP are
excluded by fmp_free_ctx, DRET/RETFMP additionally by nontermination.
The semantics of INITIAL_FMP/BUMP/FMP_PARAM/MEMTOP must be audited against
ptr/taint/shape policy or given unconditional producers.

### Completed .16 consumer experiment and exhaustive partition

The temporary `ld_singleton_consumer_probe` was checked in ExpansionEndpoint
with a `null (hyp ld_singleton_consumer_probe)` assertion, build evidence
TO_ld_mem-20261104T190123Z_m8115_t001. It used exactly the ambient DLOAD
endpoint premises with shape replaced by X=[inst] and arithmetic/assignment
membership, and exactly the endpoint conclusion with Ar=A. No source-success
or target/source successor-activity assumption was introduced. The probe and
its temporary imports were then removed (no permanent specialized API).

The checked construction is: preserve membership as a whole using
REPEAT_TCL CONJUNCTS_THEN; substitute X and h=0 explicitly, use ld_prefix_zero
to identify t0=t, project EVERY(fn_ptr_ok P) from ld_sync, get label distinctness
via ld_sync_fn_shape, and get t.idx=p from ld_sync_envelope_position. Normalize
target fuel with step_inst_non_invoke. Case split MEM_APPEND only inside the
common effect subgoal; ld_sync_arithmetic_effect/ld_sync_assignment_effect give
ss,H' unconditionally at fuel 0. Use step_inst_preserves_inst_idx for u.idx.
Abbreviate tn'=step_taint and G'=step_prov and expose their equations before
`drule_all ld_nonallocating_endpoint`. Record projections and
ld_head_order_cong discharge remaining structural obligations. Successor sync
comes solely from that common consumer and remains source-active conditional.
Uncontrolled gvs/simp unfolds the long opcode membership and normalizes supply
fields away from sync; explicit substitutions and std_ss avoid that issue.
This experiment found no missing common consumer clause.

Exhaustive partition of the opcode datatype in venomInst lines 24–68 follows.
Each constructor occurs in exactly one row (valid expansions and malformed
singletons are distinguished within the data-load row):

| Constructors | Route / status |
|---|---|
| ADD SUB MUL Div SDIV Mod SMOD Exp ADDMOD MULMOD SLT SGT ISZERO AND OR XOR NOT SHL SHR SAR SIGNEXTEND BYTE OFFSET | ld_sync_arithmetic_effect, checked consumer above |
| EQ LT GT MLOAD ILOAD | ld_sync_classified_read_effect |
| MSTORE MSTORE8 MCOPY | ld_sync_memory_write_effect |
| SLOAD TLOAD CALLER CALLVALUE CALLDATALOAD CALLDATASIZE ADDRESS ORIGIN GASPRICE GAS GASLIMIT COINBASE TIMESTAMP NUMBER PREVRANDAO CHAINID SELFBALANCE BALANCE BLOCKHASH BASEFEE CODESIZE EXTCODESIZE EXTCODEHASH RETURNDATASIZE BLOBHASH BLOBBASEFEE | ld_sync_observational_read_effect |
| SSTORE TSTORE | ld_sync_storage_write_effect |
| ISTORE | ld_sync_istore_effect |
| ASSIGN RETPC_PARAM | ld_sync_assignment_effect, checked consumer above |
| PARAM | ld_sync_param_effect |
| NOP ASSERT ASSERT_UNREACHABLE | ld_sync_identity_effect |
| CALL STATICCALL | ld_sync_oracle_call_effect |
| JMP JNZ DJMP RET RETURN REVERT STOP SINK SELFDESTRUCT INVALID DRET RETFMP | excluded by ~is_terminator; no target OK assumption needed |
| INVOKE | excluded explicitly |
| PHI | step_inst_base returns Error "phi outside prefix", contradicting target OK for singleton |
| DALLOCA GETFMP SETFMP | excluded by fmp_free_ctx at reachable source instruction (membership from ld_sync_source/ld_active_inst_member) |
| MEMTOP FMP_PARAM | excluded by fn_ptr_ok P fn at source member, NOT by raw_opcode_ok or fmp_free_ctx |
| ALLOCA | original fresh/cached allocation, audited below; unconditional effects available, assembly outstanding |
| DLOAD DLOADBYTES | valid shapes handled by accepted ld_dload_endpoint/ld_dloadbytes_endpoint; malformed singleton shape cannot return OK: exec_read1 requires one operand/one output; DLOADBYTES requires three operands (outputs ignored, so nonempty outputs are NOT malformed) |
| INITIAL_FMP BUMP | residual unconditional producers; not excluded by source shape/fmp-free; semantics update initial-fmp scalar / two outputs respectively |
| CODECOPY CALLDATACOPY RETURNDATACOPY EXTCODECOPY | residual public byte-write producers; all can return OK; RETURNDATACOPY also has an Abort branch, which does not exclude its OK branch |
| SHA3 LOG | residual memory-consumer producers; both can return OK |
| DELEGATECALL CREATE CREATE2 | residual oracle producers; all can return OK |

The MEMTOP/FMP_PARAM row corrects the earlier four-pseudo-opcode residual:
fn_ptr_ok_def lines 123–126 explicitly excludes both. ld_sync contains the
common P witness, and ld_sync_ptr_ok yields fn_ptr_ok P fn. INITIAL_FMP and
BUMP remain genuine residuals. No definition/ambient premise was changed.
For these residuals, source inspection of step_inst_base at lines 693–718,
882–935, 983–1008, 1020ff, 1096–1125 shows successful OK branches. A search of
task-created lowerDload*Script.sml found no corresponding unconditional effect
producer (the only LOG mention is the boundary observation audit).

Original allocation input audit:
* `ld_cached_alloca_effect` (SafetyAllocation lines 87–108) consumes maps/vars,
  tv equality, memory/nonghost, FRANGE H subset FDOM A, output membership and
  output in fn_pv, opcode/output shape, a cached source entry, and target OK.
  It gives source success, an exact update_var form for both states, selected
  H update support, provenance and memory/nonghost unconditionally. Allocation,
  frontier, block and index equalities follow from update_var, hence the common
  nonallocating endpoint consumer applies. Output membership and fn_pv must be
  projected from active source instruction and fn_ptr_ok; these are not extra
  frozen assumptions. Cached source/target pairing follows ld_maps.
* Fresh `ld_fresh_alloca_dispatch` gives literal size, source success and paired
  exec_alloca plus exact state updates from target OK and absent entries.
  `ld_sync_absent_alloca_key` and `ld_original_alloca_fresh` supply map-key and
  target absence using configured supply freshness; no inverse (base,size)
  lookup is needed. `ld_fresh_alloca_effect` gives the correlated H update,
  provenance and value/byte effects using fresh A'.
* `ld_fresh_alloca_structure` consumes those paired exec_alloca effects, absent
  entries/key, no private-site collision, index-adjusted g, memory/nonghost,
  lower frontiers and H' support. It gives maps/global/slots, suffix maps/vars,
  erasure preservation on all frames, intervals and charge/frontier facts
  unconditionally. Conditional next-sync still needs source next envelope and
  frame_reachable_next, as for the accepted scratch endpoint. Existing
  ld_sync_fresh_alloca_update / ld_fresh_alloca_advance are successor-conditioned
  consumers, not unconditional source-success producers.

Finite remaining singleton work (not a proof of those branches): assemble all
existing common effects and original ALLOCA; prove the eleven residual opcode
producers INITIAL_FMP,BUMP,CODECOPY,CALLDATACOPY,RETURNDATACOPY,EXTCODECOPY,SHA3,
LOG,DELEGATECALL,CREATE,CREATE2 (generalizing shared write/oracle interfaces in
place where appropriate); discharge the explicit exclusions and malformed
shape contradictions. The checked common consumer establishes the endpoint
assembly interface, not these remaining producer semantics or full coverage.

## Residual family boundary audit (checked scalar probes)

The diagnostic does not establish any residual effect producer or dispatcher.

* `ld_vars_bump_operands_equal` in SafetyValues builds from fn_ptr_ok,
  fn_shape_ok, taint_ok and ld_vars, with label equality. BUMP is neither
  pointer-preserving nor a memory reader/writer, so both operands are scalars.
  `ld_bump_output_ghosts` checks that step_prov and step_taint.t_var restrict
  away both outputs, even when their names coincide. Semantics writes ptr_out
  first and next_out second; coincident names therefore retain base+size.
  A full effect still needs a two-write ld_vars construction with empty output
  taint and restricted H; a one-output read producer is not a direct adapter.
* `ld_nonghost_initial_fmp` checks the literal initial-fmp equality needed
  by INITIAL_FMP. This is not an equality of current alloca frontiers.
* Shared byte observation already has one general boundary:
  `ld_observed_memory_read` (OracleCallAssembly, 226-249). Its required
  premises include access_ok, taint_ok, NOT about_to_revert, NOT
  in_revert_forward, a mem_read_ops witness, a source range, selected offset
  relation, and target map bounds. It excludes MLOAD/ILOAD/MCOPY/RETURN.
  Thus SHA3, LOG, DELEGATECALL and CREATE-family byte observations should
  use this boundary, not a new copy of the read proof. Zero length is handled
  there. SHA3's inline TAKE/DROP expression must be connected to read_memory.
* CALLDATACOPY/RETURNDATACOPY use common calldata/returndata from
  ld_nonghost; EXTCODECOPY uses account code agreement. Source offsets and
  lengths must agree as scalars; only destination relocates. RETURNDATACOPY
  target OK also supplies the source OOB guard after returndata equality.
  `ld_memory_write_low/slot` supply overwrite transport once equal payload
  lengths/bytes, classified destination, disjoint map bounds and the actual
  step_taint overwrite equation are established. MCOPY's accepted producer
  is snapshot-copy-specific and should not be cloned for these public copies.
* OracleCallAssembly scalar/dispatch/range assembly is explicitly limited
  to CALL/STATICCALL. ExternalBoundary's consume/adoption proof also has
  that restriction. Equal outcome queues alone do not establish any input
  equivalence. CREATE/CREATE2 use venom_create_request (data, value, salt,
  accounts, transient) and consume_create_outcome; their exact current
  request equality can be obtained from observed bytes, scalar value/salt,
  and empty storage/transient taint. taint_ok supplies those empty masks;
  ld_nonghost_accounts_empty/transient_empty supplies actual state equality.
  Missing: a create-specific consume/effect boundary retaining nonghost
  equality without demanding historical request/log equality.
* DELEGATECALL does NOT consume the create/call oracle in current semantics:
  exec_delegatecall builds make_venom_delegatecall_state and runs EVM code.
  Its inputs require current calldata bytes, target code, gas, static/call
  context, full accounts and transient equality. Empty taint obtains the
  latter two. Missing: a boundary proving equal constructed EVM states and
  correlated extract_venom_result at relocated return destinations. Treating
  DELEGATECALL as a renamed CALL would be unsound.

No additional frozen hypotheses are proposed by this audit. Full effects must
obtain the observation premises from source reachability/ambient boundaries;
this diagnostic has not proved those family-specific derivations.

## Current baseline reconciliation (2026-11-05, C1.1.1)

This section supersedes the obsolete STATE component cursor, not the proposed
semantic obligations above. All lowerDload*Script.sml theories listed here
are retained task-created helpers. No definition or theorem statement changed.
The frozen theorem at o1ContractLowerDloadMemScript.sml:16–21 matches TASK's
statement literally, including quantifiers and whitespace. Its sole `cheat`
is at line 23. A scoped grep found no cheat/admit/FAIL_TAC in the
lowerDload*Script.sml helper family. No complete endpoint dispatcher, concrete
source-return reconstruction or final reachability theorem is present.

Current checked interfaces (source signatures, not assumed preservation):

* SafetyValues:312–345 exports ld_vars_bump_operands_equal (ld_vars, equal
  labels, fn_ptr_ok, fn_shape_ok, member BUMP, taint_ok and matching t_var
  imply eval_operands equality), ld_nonghost_initial_fmp, and
  ld_bump_output_ghosts (two-output provenance/t_var DRESTRICT). The existing
  explicit null(hyp) assertion checks all three. No ld_residual_scalar_effect
  or two-write ld_vars boundary exists. SafetyUpdates:61 provides only the
  single-write ld_vars_write. Coincident BUMP outputs remain an implementation
  obligation, not a distinctness hypothesis.
* SafetyAdvance:118–143 exports ld_nonallocating_endpoint. It consumes actual
  source success, post ld_vars/memory/nonghost, erasure/support and unchanged
  allocation/control fields, along with sync/global/envelope premises. It
  supplies post vars/maps/global/domain/tail maps and successor sync only
  conditional on active_inst. Source success is NOT an assumption available
  to the missing effect producers. Its existing kernel-hypothesis assertion
  includes this endpoint and the two structural head-update boundaries.
* ExpansionEndpoint:72,160 exports ld_dloadbytes_endpoint and
  ld_dload_endpoint, with the explicit end-of-file null(hyp) assertion.
  Retain these unconditional expansion results; do not reconstruct them
  from ordinary successor coverage. SafetyAllocationCoverage exports
  ld_sync_alloca_owned_coverage with its own null(hyp) assertion; it does
  not by itself assemble the location-independent ALLOCA endpoint.
* ExternalBoundary:79–130 uses the actual event condition (nonstatic,
  changed requests AND changed outcomes AND successful head outcome) in
  ld_consume_adoption_cases/ld_consume_call_nonghost. Its opcode premise is
  CALL or STATICCALL, not delegate/create. The existing accounts_empty and
  transient_empty boundaries recover exact states from empty masks.
  The residual byte/oracle missing interfaces remain exactly those in the
  preceding audit: public overwrite payloads; SHA3/LOG current-byte reads;
  delegate EVM construction/extraction; create outcome consumption. Equal
  outcome queues are not sufficient on their own.
* SafetyRunInduction:20–71 exports the generic seven-closure
  ld_successful_run_induction, finalized at line 127. Closures are base step,
  nested successful INVOKE, ordinary suffix, nonhalting terminator, IntRet,
  block jump continuation, and block IntRet. Its conclusion is about arbitrary
  S/E/R predicates: it is NOT concrete source-return reconstruction. Added
  a null(hyp) assertion after Finalise and rebuilt successfully.

Scoped holbuild checks, all successful without source admissions in these
helpers: ExpansionEndpoint, SafetyValues, SafetyAdvance, ExternalBoundary,
SafetyRunInduction; then SafetyAllocationCoverage, SafetyControlCoverage,
TerminalSafety and OracleCallAssembly. First checks were cache hits; the
new RunInduction kernel assertion was actually executed by a rebuild.
Evidence: TO_ld_mem-20261105T144418Z_m0009_t001,
TO_ld_mem-20261105T144418Z_m0020_t001,
TO_ld_mem-20261105T144418Z_m0023_t001. Generated theorem indexes are not
available at the documented .holbuild/gen path in this checkout; no oracle-tag
index audit is claimed here, nor is final certification claimed.

Required next frontier: C1.2.1 is ready for the alias-safe scalar proof from
these current probes. C1.2.2 remains a bounded actual-consumer validation
before residual semantic implementation. C1.3.1 must instantiate the seven
closures with concrete return packages and saved-frame restoration, not
merely reuse generic induction. C1.4.1 must check all actual raw-reachable
constructors, especially atomic INVOKE and target-only terminal suffixes.
These prerequisites are currently outside the scheduler's high-risk focus;
review must authorize them before implementation. No parent semantic risk
has been reduced by this baseline audit.

## 9. Checked success-guarded package experiment (C1.3.2.1.1)

This section supersedes earlier candidate run packages, not the frozen contract.
The exact typed, capture-avoiding textual expansions are the ML quotations
`ld_probe_guard`, `ld_probe_stable`, `ld_probe_point`, `ld_probe_entry`,
`ld_probe_terminal`, `ld_probe_ambient`, `ld_probe_S`, `ld_probe_E`, and
`ld_probe_R` in `lowerDloadReturnInterfaceProbeScript.sml`. They introduce **no
HOL constants or definitions**. The following formulas spell out the packages;
all environment fields are individually quantified in S/E/R, not packaged in a
new record. Write e for lo,P,C,C',vs0,stk,fn,fn',cs,fs,f0,A0,Sigma,names.

```
Guard(k,bb,t) =
  ?z. run_block_non_phis k C' bb t = z /\
      ((?u. z = OK u) \/ (?rt u. z = IntRet rt u))

Stable(A,frames) =
  frames <> [] /\ TL frames = fs /\
  (HD frames).lf_serial = f0.lf_serial /\ ld_global lo A frames /\
  EVERY (\f. f.lf_supply = Sigma f.lf_fn.fn_name) frames /\
  EVERY (\f. !j a. j < LENGTH f.lf_Q /\ EL j f.lf_Q = SOME a ==>
    j IN P f.lf_fn.fn_name) frames /\
  (!j k. j < k /\ k < LENGTH frames ==>
    list_precedes (EL j frames).lf_fn.fn_name
                  (EL k frames).lf_fn.fn_name names) /\
  (!g. MEM g fs ==> FRANGE g.lf_H SUBSET ld_slots A fs /\
    (!a. MEM (SOME a) g.lf_Q ==> a IN ld_slots A fs)) /\
  (!a. a IN FDOM A0 /\ a IN ld_slots A0 fs ==>
    FLOOKUP A a = FLOOKUP A0 a)

Point(e,bb,t) =
  ?PG G tn inst s t0 A frames N X p h.
    ld_sync lo P C vs0 stk PG G tn fn inst s t0 A frames N /\
    Stable(A,frames) /\ fn' = ld_image (HD frames) /\
    ld_envelope (HD frames).lf_supply fn s s.vs_inst_idx X p /\
    ld_prefix C' fn' X p h t0 t /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb /\
    ld_return_cont C fn cs s

Entry(e,q) =
  !k bb tp. lookup_block q.vs_current_bb fn'.fn_blocks = SOME bb /\
    eval_phis q bb.bb_instructions = OK tp /\
    Guard(k,bb,tp with vs_inst_idx := phi_prefix_length bb.bb_instructions) ==>
    Point(e,bb,tp with vs_inst_idx := phi_prefix_length bb.bb_instructions)

Terminal(e,rt,u) =
  ?sf rs cs' Ar fr tnr rinst se te PG' G' Nr.
    run_blocks sf C fn cs = IntRet rs cs' /\
    ld_sync lo P C vs0 stk PG' G' tnr fn rinst se te Ar fr Nr /\
    Stable(Ar,fr) /\ rinst.inst_opcode = RET /\
    step_inst 0 C rinst se = IntRet rs cs' /\
    step_inst 0 C' rinst te = IntRet rt u /\
    rs.iret_values = rt.iret_values /\
    rs.iret_adopt_fmp = NONE /\ rt.iret_adopt_fmp = NONE /\
    ld_memory lo Ar tnr cs' u /\ ld_nonghost tnr cs' u /\
    (!a. a IN ld_slots Ar fs ==>
      FLOOKUP (DRESTRICT Ar (ld_slots Ar fs)) a = FLOOKUP Ar a)

Ambient(e) =
  o1_ctx_shape C /\ o1_run_state_ok vs0 /\
  reserved_intervals_wf C.ctx_global_reserved /\ fixed_region_reserved lo C /\
  ptr_discipline lo C vs0 /\ fmp_free_ctx C /\
  mem_inv raw_mem_ok C vs0 /\ mem_inv dload_offset_ok C vs0 /\
  mem_inv dload_headroom_ok C vs0 /\ callee_first names C.ctx_functions /\
  (!f. MEM f C.ctx_functions ==>
    lookup_function f.fn_name C'.ctx_functions =
      SOME (FST (lower_dload_function_supply (Sigma f.fn_name) f))) /\
  fn' = FST (lower_dload_function_supply (Sigma fn.fn_name) fn)

Outcome(e,z) = case z of OK q => Entry(e,q)
  | IntRet rt u => Terminal(e,rt,u) | _ => T

S k ctx ti t z = !e bb. ctx=C' ==>
  Ambient(e) /\ Point(e,bb,t) /\ get_instruction bb t.vs_inst_idx = SOME ti ==>
  (case z of OK q =>
    if is_terminator ti.inst_opcode then (~q.vs_halted ==> Entry(e,q))
    else (!j. Guard(j,bb,q with vs_inst_idx := SUC t.vs_inst_idx) ==>
      Point(e,bb,q with vs_inst_idx := SUC t.vs_inst_idx))
   | IntRet rt u => Terminal(e,rt,u) | _ => T)
E k ctx bb t z = !e. ctx=C' ==>
  Ambient(e) /\ Point(e,bb,t) ==> Outcome(e,z)
R k ctx fnT q z = !e. ctx=C' ==>
  Ambient(e) /\ fnT=fn' /\ Entry(e,q) ==>
  (case z of IntRet rt u => Terminal(e,rt,u) | _ => T)
```

### Checked results and limits

`ld_probe_conditional_induction` instantiates `ld_successful_run_induction`
**once**, with precisely the above S/E/R. Alias equality premises pin its three
families to the concrete Ambient, Point and Terminal quotations. The proof then
forgets these equalities and proves the five compositional closures abstractly:
nonterminating suffix, terminator OK, instruction IntRet, run recursion and
block IntRet. Each Resume is under five tactic lines; no semantic definition is
unfolded there. Its only remaining semantic premises are the base-step and
nested-INVOKE producers, exactly as quantified in the generic induction. All
seven generic closures have therefore been checked conditionally, not proved
unconditionally.

`ld_probe_entry_body` consumes Entry, lookup, successful PHIs, and a successful
body equation to produce Point. `ld_probe_terminal_invoke` projects the actual
source run and equal return vector out of the concrete Terminal package and
feeds the unchanged `ld_invoke_from_return`. `ld_probe_run_return` consumes the
run conclusion of the conditional induction, Ambient, a successful target run,
and **Entry at the initial setup state** to extract Terminal. This last Entry
premise is the third semantic producer group: no claim deriving it from setup
has been proved. The conditional induction itself needs no initial Entry
producer because R is an implication *from* Entry. Null-kernel-hypothesis
assertions check all four new theorems (and the existing INVOKE consumer).

Missing concrete semantic work, deliberately NOT discharged by this probe:

1. Base-step producer: strict-prefix stuttering; endpoint source advancement;
   success-guarded successor alignment; branch-to-Entry transfer; RET-to-Terminal.
   Target suffix success alone is not source activity. In particular endpoint
   conditional synchronization still needs a proved alignment/inversion bridge.
2. Nested-INVOKE producer: actual setup witnesses and a fresh independently
   quantified callee origin; initial callee Entry; use of the R IH; then concrete
   merge/adopt/bind/pop preservation of Stable and Point/Entry. Equal values and
   existence of source execution are all the elementary consumer currently
   validates; it does not establish the ghost restoration clauses.
3. Initial/pre-entry producer: synchronized source/target entry, source
   frame_reachable_block and PHI/provenance transfer, preservation of saved tails
   and the fixed-origin return continuation. Entry deliberately makes no claim
   about unsuccessful PHI or suffix executions.
4. Stage-derived availability of the fixed Ambient, configured supply freshness
   (`ir_supply_covers_fn`), and any per-point non-revert facts used by endpoint
   theorems. They have not been smuggled into Ambient as new hypotheses.
5. RET-only terminal behavior uses unchanged `fmp_free_ctx C`, not the obsolete
   claim that fn_ptr_ok alone excludes RETFMP/DRET. Terminal carries no demand
   for activity at a returned state and never uses ld_prefix at an endpoint.

Verification: `holbuild(targets=['lowerDloadReturnInterfaceProbeTheory'])` passes
without cheats; the frozen stage theorem has not been changed by this experiment.
