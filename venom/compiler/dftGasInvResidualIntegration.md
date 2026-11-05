# C1.4.7: oracle residual integration audit

This is a diagnostic, not a proved correspondence. No definitions or theorem
statements in existing theories have been changed. In particular the candidate
contracts below are **unproved**, and are not assumptions available to clients.

## Source audit: where the existing argument really works

The relevant chain in `dftRunRelScript.sml` is:

* `dft_run_block_gas` (2939-3038): strips the common pseudo prefix, obtains
  `dft_block_head_bubbles`, initializes `dft_remaining_inv`, and invokes
  `dft_head_bubbles_variant`. Its conclusion is
  `?s. s' = s with vs_gas_readings := s'.vs_gas_readings /\
       dft_res_rel (run_block fuel C bb s) (run_block fuel C bb' s')`.
  Both executions use **C** and list GAS readings, not event-indexed GAS.
* `dft_head_bubbles_variant` (2855): induction over syntactic head extraction.
  Its step uses `dft_extract_head_variant` (2802) and propagates
  `dft_remaining_inv_step` after successful execution of the extracted head.
* `dft_remaining_inv fn bb todo s` (524) contains source membership and order
  of remaining instructions, strict dominator definitions, availability of
  outputs of removed producers, block-label equality and label availability.
  It does NOT assert that an actual original-order prefix reached s.
* `dft_remaining_inv_ready` (581) derives defined variable operands of a
  selected head y from `todo = pre ++ y::post`, `pre <> []`, and
  `EVERY (\x. ~dft_must_order x y) pre`. It needs `wf_ssa`, `wf_function`,
  and block membership. Its label conclusion excludes INVOKE and CODECOPY.
* `dft_remaining_inv_step` (550) needs a successful **step_inst** at the
  selected y and removes y from todo. Its proof depends on list-step frame,
  producer and dominator preservation; replacing the step premise by ev_step
  is not justified by the exported theorem.

The smallest reusable structural unit is therefore the head-bubble relation
plus remaining-instruction readiness, NOT the final run_block theorem.
The smallest semantic unit to replace is the pair/suffix swap family.

Exact successful pair boundary (1902), with its assumptions retained:

```sml
dft_gas_swap_pair x y /\ ~gas_pair x.inst_opcode y.inst_opcode /\
inst_wf x /\ inst_wf y /\
step_inst fuel C y s = OK sy /\
step_inst fuel C x (sy with vs_inst_idx := SUC s.vs_inst_idx) = OK syx ==>
?sx sxy. step_inst fuel C x s = OK sx /\
  step_inst fuel C y (sx with vs_inst_idx := SUC s.vs_inst_idx) = OK sxy /\
  (sxy with vs_inst_idx := SUC (SUC s.vs_inst_idx)) =
  (syx with vs_inst_idx := SUC (SUC s.vs_inst_idx))
```

This requires TWO successful steps. It cannot move a source instruction x
before the current target observation y when x has not yet executed there.
`dft_nongas_suffix_swap` (2627) handles this by exhaustive cases on source x
and source y after x, not by assuming success: source Error cases invoke
`dft_nongas_suffix_swap_error` (2474), which excludes target OK and IntRet;
source abort cases invoke first/second-abort transport, with guarded totality
and defined operands for the partner. Those exclusion results work for a
COMPLETED suffix. An arbitrary prefix ending before x is a different consumer.

`dft_res_rel` (16) makes this distinction precise: source Error rules out
only target OK and IntRet; source Abort allows a possibly different abort
state. Thus a completed target IntRet forces a source IntRet once a relational
suffix theorem has been established. A reachable instruction is not an IntRet.

`dft_gas_suffix_swap` (2676) existentially changes source readings and has a
special GAS/INVOKE branch. The oracle version must instead keep
`orc (p,d,inst.inst_id)` fixed; neither its conclusion nor its proof can be
reused verbatim. `dft_nongas_pair_success` (1884) ultimately uses
`step_swap_ok_ext` or external-call/assertion variants, all with step_inst and
the same callee context. They are not parameterized by an INVOKE handler.
There is no exported generic handler kernel in the inspected chain.

## Residual relation candidate and precise integration failure

A useful *virtual* residual state would have parameters
`orc p d C D fn bb entry completed todo virtual_state` and satisfy the
following HOL-shaped conjunction (notation is schematic, not a definition):

```sml
PERM (completed ++ todo) (FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions) /\
ALL_DISTINCT (MAP (\i. i.inst_id) (completed ++ todo)) /\
dft_remaining_inv fn bb todo virtual_state /\
(* virtual_state is reached by executing completed under event-indexed steps *)
virtual_exec orc p d C completed entry virtual_state
```

Executed IDs are `MAP inst_id completed`; `todo` remains in original source
relative order. A target executed list is related to `completed` by extraction
squares. At synchronized cuts, nonvariable fields must agree except
vs_inst_idx and vs_gas_readings; for every variable live in todo, FLOOKUP of
vs_vars must agree. Relevant fields include memory, transient storage,
accounts, logs, outcomes, requests, pending deletions, returndata, immutables,
FMP, initial FMP, labels, caller context and block/previous labels. Equal
numeric operands alone is insufficient to preserve later INVOKE setup.

**Failure:** this is a virtual execution predicate, not an actual source
prefix witness. Simply conjoining

```sml
?n ss. inv_ev_prefix orc p d C bb n source_entry ss /\
       live_agreement todo ss virtual_state
```

does not give an inductive relation for selecting the next target head.
The witness ss may already have executed that head while processing an
earlier source prefix; conversely source-earlier instructions may be absent
from completed. Requiring matching executed ID sets is false for ordinary
independent reorderings. Dropping that requirement leaves no transition
that constructs the next genuine original-order prefix. This diagnostic
therefore does NOT certify the above as an end-to-end residual interface.

The missing prefix kernel, stated at its real consumer, is:

```sml
(* head y is next in the transformed schedule; all shape, SSA,
   readiness, effect and head-bubble assumptions must be supplied *)
target_prefix_reached_y /\ head_extraction_certificate ==>
?m ss source_y.
  inv_ev_prefix orc p d C bb m source_entry ss /\
  get_instruction bb ss.vs_inst_idx = SOME source_y /\
  source_y.inst_id = y.inst_id /\
  memory_operand_agreement source_y ss y target_state /\
  ss.vs_initial_fmp = target_state.vs_initial_fmp
```

In particular this requires success of every source instruction before y
that is absent from the target prefix. Two-success commutation supplies no
such success. Needed classification: each crossed instruction is either
provably total at a ready state or its potential failure/nonreturn would
force a must-order edge preventing this crossing. No inspected theorem
exports this classification for oracle INVOKE and arbitrary prefixes.

## Initialization and projection obligations

At entry, `completed=[]`, `todo=source nonpseudo body`, and virtual state is
the post-PHI state. `dft_remaining_inv_initialized` (910) is the existing
list-semantics producer of readiness; its use in dft_run_block_gas at 3015
needs actual source run/phi witnesses. An oracle initialization proof must
establish strict_dom_vars_defined, labels and nonstatic context from frozen
entry/setup hypotheses, transport the unchanged PHI prefix, and adapt the
frame/producer proof of remaining_inv_step to ev_step. These obligations
remain **unproved**; source membership and PERM alone do not establish them.

An actual prefix witness with endpoint instruction, block membership and
label equality feeds the proved `inv_ev_prefix_reachable`. The observation
projection then needs equality of inst_mem_ranges plus initial FMP equality
(and the separate concrete forwarding implication). Flipped operands require
the opcode-specific range observation argument; inst_id equality alone does
not give range equality. None of these projections may use a virtual prefix
as though it were inv_ev_prefix.

## Returning-run reflection and induction diagram (unproved)

Conditional block consumer:

```sml
callee_IntRet_reflection_at_fuel k /\ related_block_entry s t /\
ev_block orc p d k D bb' t = IntRet ret u ==>
?v. ev_block orc p d k C bb s = IntRet ret v /\ result_frame_agreement v u
```

Also needed: the analogous OK block continuation (including chosen label),
and observation transport for finite partial prefixes. The callee hypothesis
must be for related setups, not arbitrary same states. INVOKE success yields
an actual IntRet callee run by ev_step_invoke_OK; output arity, adopt_return_fmp
and merge_callee_state then need relation-preserving plumbing.

Well-founded arrangement from the frozen equations:

1. Prove ev_blocks reflection at fuel N by complete induction on N.
2. N=0 cannot return. At N=SUC k, PHIs lead to ev_block at fuel k and depth
   SUC d. An INVOKE in this block uses ev_blocks at fuel k, so the outer IH
   applies, with path ((SUC d,id)::p) and initial depth SUC d.
3. Recursive block continuation also uses ev_blocks at fuel k. Within a block,
   fuel is constant: induction on finite head extraction/residual length is
   separate. Do not claim each ev_step reduces fuel.
4. In ev_reachable next, finite fuel is chosen separately for each successful
   step. A returning call can use the already established reflection theorem
   at that chosen fuel. In ev_reachable callee, only decode/setup/entry are
   given; transport the call observation and setup, then enter the source
   callee WITHOUT invoking return reflection or assuming termination.

## Adversarial interface tests (symbolic, not EVAL theorems)

* Independent assignments: source [a,b,y], target [b,y,a] can observe y before
  a. A relation equating target executed IDs with a source prefix is rejected.
  A witness for source y must execute a and b; totality/readiness of a is the
  precise missing producer, not PERM.
* GAS-defined address: a GAS defining g must precede MLOAD g by SSA readiness.
  Relocated GAS must read the same (p,d,id), NOT an arbitrary list reading.
  Live-variable agreement must include g; gas_variant alone permits no
  disagreement in g. Existing GAS existential input adjustment is rejected.
* Returning INVOKE then memory: source/target call setups must agree on args
  and shared state; successful target call supplies finite IntRet. Smaller-fuel
  reflection supplies the source result; merge/bind preservation then supplies
  the memory observation. None follows from the non-INVOKE ev_step equation.

## Diagnostic conclusion

The source audit identifies a plausible reusable *structural* layer and an
actual missing semantic kernel, but does not validate a coherent actual-prefix
residual relation. The next strategy decision must choose/prove the oracle
crossing classification (including nonreturning INVOKE), or change the residual
architecture. Adding another conditional prefix helper would hide the same
gap. No general simulation is claimed by this report.

## Checked boundary and actual-edge interfaces (C1.4.9.17/.18)

`dftGasInvBoundaryStateTheory` now defines
`inv_boundary_eq s t <=> (s with vs_inst_idx := 0) = (t with vs_inst_idx := 0)`.
Its checked consumers are exact merge equality (`inv_boundary_merge`), exact
setup equality (`inv_boundary_setup`), PHI result equality after resetting both
indices to any k (`inv_boundary_phis`), successful terminator boundary
congruence (`inv_boundary_terminator`), and current-label equality. Gas readings
and every non-index field remain exact. This is not a DFT simulation theorem.

`dftGasInvOracleAvailabilityTheory` proves successful oracle-step FDOM
monotonicity under `inst_wf`, output membership, and successful-step exclusion
of PHI. It reuses `inv_ev_step_availability` for the nonterminator domain/frame
identity rather than duplicating that proof. Actual `ev_block` execution has
FDOM monotonicity, nonterminator-output coverage from the initial cursor onward,
initialized earlier-output coverage, and final membership in `bb_succs bb`.
The last interface needs `bb_well_formed bb` and `EVERY inst_wf` but no entry
cursor or acyclicity assumption.

The checked main interface is:
```sml
wf_function fn /\ ssa_form fn /\ MEM bb fn.fn_blocks /\
bb.bb_label = s.vs_current_bb /\ fn_reachable fn s.vs_current_bb /\
strict_dom_vars_defined fn s /\ EVERY inst_wf bb.bb_instructions /\
eval_phis s bb.bb_instructions = OK u /\
ev_block orc p d fuel ctx bb
  (u with vs_inst_idx := phi_prefix_length bb.bb_instructions) = OK t /\
~t.vs_halted ==>
fn_reachable fn t.vs_current_bb /\ strict_dom_vars_defined fn t
```
It uses actual oracle transitions (including successful INVOKE through existing
bind_outputs/domain facts), not conversion to list-semantics execution. Thus
loop-edge dominance transfer is available independently of reflection.

Remaining integration obligations: full-block sorting/reconstruction with
exact boundary states; result cases other than OK; smaller-fuel returning-call
reflection; initial/post-pseudo readiness and actual label-operand availability
at arbitrary entered blocks; and concrete forwarding preservation. These
interfaces do not assume or establish any of those missing results. In
particular label availability is still a separate initialization requirement;
no label producer is claimed here.
