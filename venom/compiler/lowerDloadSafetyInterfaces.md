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
    mem_inv dload_headroom_ok C vs0 /\ callee_first names C /\
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
