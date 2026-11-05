# C1.5.2 — recursive runner interface audit

Diagnostic only. No theorem or definition is introduced by this document.
Baseline: o1ContractLowerDloadSimTheory builds (TO_m6571); its original main
cheat is still present. This is not a simulation certificate.

## 1. Literal recursion and induction

venomExecSemanticsScript.sml:1663–1740 defines precisely three modes.
The termination rank is lexicographic:

| mode | rank |
|---|---|
| step_inst k C i s | (k,1) |
| exec_block k C b s | (k,2 + LENGTH b.bb_instructions - s.vs_inst_idx) |
| run_blocks k C f s | (k,0) |

The generated run_defs_ind is used with all three predicates in
venomExecProofsScript.sml:968–978. Its live call premises are visible in the
checked fuel_mono proof at 988,1007,1018,1051,1078. In particular it supplies:

* step mode: run mode at (k,C,callee,cs), conditional on successful decode,
  lookup, argument evaluation, and setup. Same fuel, smaller rank component.
* exec mode: step mode at the fetched instruction; exec mode at the source
  nonterminator OK successor with index overwritten by SUC of the OLD index.
* run mode at SUC k: exec mode at (k,C,bb,post_phi_state), and run mode at
  (k,C,fn,block_result) when that result is OK and not halted.

Thus fuel-only induction is not the literal recursion induction. It would
require a nested instruction-distance induction. callee_first does not
supply any of these semantic IHs.

## 2. Exact candidate propositions (textual abbreviations only)

To make the candidates legible without authorizing definitions, the following
are **textual macros**. Replace every occurrence by its right-hand HOL term,
renaming bound variables to avoid capture. They are not conjectured lemmas or
new constants. Each displayed mode is universally closed over all free
variables, including the static parameters rpolicy, view, names, vs, C, C',
lo and D. The four-argument prefix of a mode is exactly the run_defs_ind
prefix. All ghost/frame parameters occur AFTER that prefix.

```
A := ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
     dead_wf D /\ o1_ctx_shape C /\ o1_run_state_ok vs /\
     o1_src_inv D C vs /\ callee_first names C.ctx_functions /\
     ptr_discipline lo C vs

J(stk,PG,G,tn,fn,i,s,t,n,a,U,B,HP,H,sites,X,ts) :=
  ld_joint_boundary vs C C' lo D stk PG G tn fn i s t
    n a U B HP H sites X ts
```

Use result packets that do NOT equate internal return with observable exit.
Here is the exact candidate common result relation for exec/run, with initial
frame parameters stk,PG,fn,a,U,HP,ts and initial address A0 held fixed:

```
R(r,r') :=
  (case r of
     Halt se => (?te. r' = Halt te /\ dead_result_rel D r r')
   | Abort ab se => (?te. r' = Abort ab te /\ dead_result_rel D r r')
   | Error e => F
   | IntRet ir se =>
       ?kr ri sr tr nr Gr tnr Br Hr sitesr Xr jr.
         ri.inst_opcode = RET /\ active_inst fn ri sr /\
         J(stk,PG,Gr,tnr,fn,ri,sr,tr,nr,a,U,Br,HP,Hr,sitesr,Xr,ts) /\
         step_inst kr C ri sr = IntRet ir se /\ se = sr /\
         sr.vs_call_ctx.cc_address = A0 /\
         step_inst kr C' ri tr = IntRet jr tr /\ r' = IntRet jr tr /\
         jr.iret_values = ir.iret_values /\
         ir.iret_adopt_fmp = NONE /\ jr.iret_adopt_fmp = NONE
   | OK se =>
       ?kb bi sb tb nb Gb tnb Bb Hb sitesb Xb te.
         MEM bi.inst_opcode [JMP; JNZ; DJMP] /\ active_inst fn bi sb /\
         J(stk,PG,Gb,tnb,fn,bi,sb,tb,nb,a,U,Bb,HP,Hb,sitesb,Xb,ts) /\
         step_inst kb C bi sb = OK se /\
         step_inst kb C' bi tb = OK te /\ r' = OK te /\
         se.vs_current_bb = te.vs_current_bb /\
         se.vs_prev_bb = te.vs_prev_bb /\
         se.vs_call_ctx.cc_address = A0)
```

This intentionally returns the WHOLE pre-branch boundary, not a fictitious
boundary at a branch target before PHIs. It lets the run case use
ld_joint_branch_entry once the *source continuation* proves successful entry.
The r' existential for Halt/Abort is redundant but pins the constructor.
The candidate is still unproved: coverage of all OK terminators and return
address persistence must be checked, not assumed. Target fuel for the packet's
local RET/branch equation is arbitrary non-INVOKE fuel and need not equal its
outer runner fuel.

Candidate exec predicate:

```
!k ctx bb s.
  !stk PG G tn fn i t n a U B HP H sites X ts r.
    ctx = C /\ A /\ opaque_use_ok fn /\ ~s.vs_halted /\
    J(stk,PG,G,tn,fn,i,s,t,n,a,U,B,HP,H,sites,X,ts) /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME i /\
    exec_block k C bb s = r /\ terminates r ==>
    ?m fn' bb' r'.
      lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
      lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
      exec_block m C' bb' t = r' /\ R(r,r')
```

In this use of R take A0 = s.vs_call_ctx.cc_address. Ghost maps/counters can
change; frame owner, saved source/target callers, frame parameters and stack
shape are fixed across execution within the current function. Fresh counters
must be threaded from the returned packet, not reset to the entry n.

Candidate run predicate (BEFORE PHI entry):

```
!k ctx fn s0.
  !stk PG G tn i s1 t0 t1 n a U B HP H sites X ts r.
    ctx = C /\ A /\ opaque_use_ok fn /\ ~s0.vs_halted /\
    enters_block fn s0 s1 /\
    (?fn'. lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
           enters_block fn' t0 t1) /\
    J(stk,PG,G,tn,fn,i,s1,t1,n,a,U,B,HP,H,sites,X,ts) /\
    run_blocks k C fn s0 = r /\ terminates r ==>
    ?m fn' r'. lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
      run_blocks m C' fn' t0 = r' /\ R(r,r')
```

Here A0 = s0.vs_call_ctx.cc_address. The enters_block witnesses are semantic
entry transitions only, NOT assumed target callee executions. Entry fetch is
ld_wf_enters_block_fetch. This preentry mode avoids evaluating PHIs twice on
s1/t1. Relation J already contains activity/control at s1/t1. The mode must
ultimately show its R never returns OK (reuse run_blocks_not_OK).

Candidate step predicate needs to cover only INVOKE; all non-INVOKE assembly
is performed directly in the exec case by checked local kernels. This avoids
an invalid same-instruction target step claim for DLOAD expansions:

```
!k ctx callinst s.
  !stk PG G tn fn t n a U B HP H sites X ts r.
    ctx = C /\ A /\ opaque_use_ok fn /\ ~s.vs_halted /\
    J(stk,PG,G,tn,fn,callinst,s,t,n,a,U,B,HP,H,sites,X,ts) /\
    active_inst fn callinst s /\ callinst.inst_opcode = INVOKE /\
    step_inst k C callinst s = r /\ terminates r ==>
    ?m r'. step_inst m C' callinst t = r' /\
      (case r of
         OK s1 =>
           ?next t1 nr Gr tnr Br Hr sitesr Xr.
             r' = OK t1 /\
             J(stk,PG,Gr,tnr,fn,next,
               (s1 with vs_inst_idx := SUC s.vs_inst_idx),
               (t1 with vs_inst_idx := SUC t.vs_inst_idx),
               nr,a,U,Br,HP,Hr,sitesr,Xr,ts) /\
             active_inst fn next
               (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
             s1.vs_call_ctx.cc_address = s.vs_call_ctx.cc_address
       | Halt se => (?te. r' = Halt te /\ dead_result_rel D r r')
       | Abort ab se => (?te. r' = Abort ab te /\ dead_result_rel D r r')
       | IntRet ir se => F
       | Error e => F)
```

This candidate step conclusion is missing a general counter/scope monotonicity
projection if the next preservation lemmas need more than J. Do not hide this
inside a proof. More importantly its OK case is NOT an immediate consequence
of ld_joint_boundary_call: it requires the run IH's actual RET endpoint packet.

## 3. Endpoint linkage and exact return obligations

ld_joint_boundary_return (lines 10–37) consumes a boundary at callee RET,
not the return value alone. Its input ghost parameters MUST be those returned
by the run IH. Its saved head f is the record installed by
ld_joint_boundary_call (lines 65–70), caller' is the saved original target t,
and the callee owner is the fresh entry n. The run packet keeps that owner and
saved head unchanged, while allowing its fresh counter and maps to evolve.

The source step equation for INVOKE supplies:

* actual source callee run = IntRet ir se;
* actual successful bind_outputs on merge_callee_state f.cf_state se;
* the callee RET packet supplies sr=se, its live boundary and target tr;
* return-boundary yields actual target bind, identical return values, no FMP
  adoption, restored whole successor boundary and restricted maps.

Two extra return premises cannot be waved away:

1. **Caller successor activity.** The successful bind changes vars only;
   merge_callee_state restores caller control. Together with wf_function,
   active_inst at the saved INVOKE, and INVOKE not being a terminator,
   ld_nonterminator_successor produces next. No assumption that the callee
   returned proves this by itself. Need a checked short bridge for the exact
   merged/bound state, or discharge these equations at assembly time.
2. **Address provenance.** Need sr.cc_address = f.cf_state.cc_address.
   ld_joint_boundary_call provides entry-address equality; J only gives
   cross-run local-field equality, not equality to a saved caller. The R packet
   explicitly propagates equality to A0. No exported universal preservation
   theorem was located in this audit. This is a real missing proof boundary
   (or induction strengthening), not a license to add the equality as an
   unsupported hypothesis to final simulation.

If source lookup/setup/bind fails, step result is Error and the terminating
antecedent eliminates the case. If source execution propagates Halt or Abort,
no caller continuation is required. Target callee endpoint is obtained by IH,
never assumed. Internal IntRet is NOT dead_result_rel.

## 4. Composition / decrease / target fuel table

| source branch | consumed interface | source decrease | target witness / endpoint |
|---|---|---|---|
| ordinary nonterminator OK | ld_joint_ordinary_next | exec instruction distance | synchronize local step and recursive suffix, whole J |
| original ALLOCA OK | fresh/repeated next boundaries | exec instruction distance | target original allocation, suffix at incremented PC |
| DLOAD / DLOADBYTES | ld_joint_dload_continue / ld_joint_dloadbytes_continue | one SOURCE instruction distance | exec_block equality through 4/2 generated instructions, not one target step |
| INVOKE successful setup | ld_joint_boundary_call, invoke argument interfaces | step(k,1) to run(k,0) | run IH on cs/ct, actual callee result |
| INVOKE IntRet callee | RET packet + ld_joint_boundary_return | same run IH, then exec continuation IH | callee witness gives target step witness; restored J at caller successor |
| INVOKE Halt/Abort callee | run IH observable packet | same run IH | identical outer result propagation, no restoration |
| INVOKE malformed or callee Error/OK | literal step_inst equation | none | excluded by terminates and run_blocks_not_OK |
| branch OK | ld_joint_branch_step | exec to step rank | pre-branch J packet plus actual OK target result |
| run_blocks branch continuation | packet + ld_joint_branch_entry + successful fetch | SUC k to k | max(block witness, tail witness)+1 |
| RET IntRet | ld_joint_ret_step | exec to step rank | full pre-RET J packet, se=sr, target tr |
| Halt non-INVOKE | ld_joint_halt_result | exec to step rank | dead_result_rel |
| Abort ordinary / revert suffix | abort/forward-abort interfaces | source exec recursion or checked suffix | dead_result_rel; forward-revert mode must be dispatched separately |
| run entry PHI | paired enters_block witnesses, ld_wf_enters_block_fetch | SUC k to exec k | target exec witness+1; no double PHI |
| run fuel 0 / fetch absent / PHI error | literal equations | none | non-Error source excludes |
| root | root entry assembly + run mode + ld_root_result_shape | wrapper only | existential run_context target fuel |

The forward-revert suffix is deliberately not claimed covered by ordinary J
preservation: ld_joint_ordinary_next has ~in_revert_forward. The existing
suffix abort boundary must discharge it at exec level. Static root-entry
assembly, all OK terminator coverage, exact fetch at saved caller, and source
address persistence remain to be validated in the implementation PLAN.

## 5. Fuel synchronization is legal only for non-Error results

venomExecPropsScript.sml:406 and venomExecProofsScript.sml:956 export fuel_mono:
for each of step_inst/exec_block/run_blocks,
`F n = r /\ (!e. r <> Error e) /\ n <= m ==> F m = r`.
o1PassLiftScript.sml:280–305 exports terminates_not_error and the three
*_terminates_mono wrappers. These preserve the EXACT state/result, including
internal IntRet, not just its observations.

Within exec_block all instructions use one fuel. If the recursive suffix
needs m2 and an INVOKE needs m1, use MAX m1 m2; lift each actual non-Error
execution with its corresponding conjunct of fuel_mono. For generated
non-INVOKE segments one may instantiate the segment equations at this same
fuel. At run_blocks use SUC(MAX block_fuel tail_fuel), since both recursive
calls use predecessor fuel. A callee can return IntRet (non-Error), so it can
be lifted before reconstructing INVOKE. Never lift Error, and never replace
callee fuel with source fuel without a mono argument.

## Review request

These are fully specified candidate modes, not validated preservation
statements. The audit exposes two durable obligations before runner work:
source call-address preservation and exact saved-caller nonterminator
successor/fetch assembly. It also exposes the need for a terminal/branch/RET
result packet or equivalent CPS interface; dead_result_rel alone cannot be
the mutual IH. Strategist should review the shallow C1.5 subtree rather than
append more opcode descendants. No definitions, theorem statements, or SML
files were changed during this diagnostic.

## 6. Checked endpoint consumer checkpoint (C1.5.7)

`o1LowerDloadEndpointConsumerTheory` now checks two existential packet
consumers, without asserting existence of any callee run:

* `ld_return_endpoint_consume`: supplied actual source RET equation, target RET
  equation and whole pre-RET J, with fixed saved head `f`, owner `a`, `ofr`,
  and saved target `caller'`. The packet address equals A0 and A0 equals the
  saved source caller address. A successful actual source bind, saved INVOKE
  activity, `wf_function f.cf_fn`, pointer discipline and callee opaque-use
  validity suffice. `ld_ret_endpoint` derives `se=sr`; the INVOKE successor
  lemma derives the caller's next instruction. The return boundary reconstructs
  the actual target bind and the full caller successor J. No target callee run
  is inferred from an entry state. The target `jr` supplied in the packet is
  identified with the reconstructed RET result by the two actual step equations.
* `ld_branch_endpoint_consume`: supplied actual branch OK equations, pre-branch
  J and matching target control, source `wf_function`, successful source
  `enters_block fn se s1` and nonhalted `se` suffice. Entry fetch supplies the
  actual `next` and source block/fetch equations; branch entry constructs target
  entry and post-PHI J. It also propagates the address A0 and nonhaltedness to
  `s1`. This is precisely the preentry run-mode interface, not a second PHI
  evaluation on `s1`.

Both consumers retain the endpoint's `n`, `G`, `tn`, `B`, `H`, `sites`, `X`:
these names denote the *evolved* packet parameters. Return restricts the maps
and restores the saved caller frame owner/parameters; branch applies entry
provenance/taint updates. Neither consumer resets fresh counters. No extra
counter monotonicity premise was needed for these compositions. This does not
prove that the execution induction can construct every packet; in particular,
any counter/scope requirements of call and allocation kernels still have to
be matched against J by that induction.

The three candidate modes above now explicitly require nonhalted source input:
exec and step use `~s.vs_halted`, run uses `~s0.vs_halted`. Root entry discharges
this; `ld_step_ok_halted` and `ld_enters_block_halted` propagate it. Step Halt
and Abort alternatives now pin the target constructor and the SAME abort tag,
just like R. An already-halted OK block result is therefore not silently
classified as a branch endpoint.

Packet RET and branch equations are fuel independent by the existing
`step_inst_non_invoke` (venomExecSemantics:1829-1834): each equals
`step_inst_base inst s` when the opcode is not INVOKE. RET and all three branch
opcodes meet this condition. This is why the consumer's common `kb` in the two
branch equations is legitimate even when assembled from different local fuel
witnesses. Do not apply this fact to INVOKE or use it to lift an Error run.

Result coverage remains exactly the table in section 4: nonterminator OK
continues with whole J; branch OK returns a pre-branch packet; RET returns a
pre-RET packet; Halt/Abort preserve constructor/tag and observations; Error is
excluded by termination; run never returns OK. Successful INVOKE binds the
actual internal return, whereas callee Halt/Abort propagate without restoring
caller locals. Revert-forward suffix execution remains a separate exec case.

The earlier 'Review request' is historical diagnostic context. Local address,
root entry, saved caller successor and endpoint consumption are now checked;
the common three-mode simulation itself is still unproved and must receive
strategist review before implementation. The original frozen main cheat is
unchanged. No new relation definition was introduced.
