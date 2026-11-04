# Post-control operational design checkpoint

Scope: C1.preservation.execution.closure. Specification material only; no
new HOL definition, theorem claim, or evidence of falsehood.

The accepted E0093 report in lowerDloadOperationalClosure.md remains intact.
Every residual there remains an obligation except for same-state structural
entry/position computation, now supplied by lowerDloadControlPositionTheory.

## Checked control interface

* lower_dload_insts_supply_position (existing ancestor): explicit prefix,
  selected expansion, suffix, supplies, and local offset j.
* lower_dload_insts_supply_segment_index: forward source and target indices.
* lower_dload_insts_supply_phi_length and lower_dload_insts_supply_eval_phis:
  exact computation on the same input state, including failures.
* lower_dload_blocks_supply_lookup and its forward counterpart: first matching
  block lookup, without a unique-label hypothesis.
* lower_dload_function_supply_enters_block: actual same-state entry iff.
* lower_dload_function_supply_active_origin: target active position has an
  actual configured source expansion origin.

The last two do NOT imply entry on related but different variable maps, nor
source active_inst at a target numeric PC. They discharge the structural part
of E0093's missing position specification, not its relational semantics.

## Exact reserve expressions and a remaining representation choice

The ledger candidate keeps As : num set list, one actual scratch set per
suspended target frame, in nearest-caller-first order. At a synchronized
boundary require:

    LENGTH As = LENGTH astk /\ LENGTH astk = LENGTH bstk
    EVERY FINITE (A::As)
    d = 32 * SUM (MAP CARD As)
    ld_alloc_account keys d A s t

Each saved frame at depth h must use displacement
`32 * SUM (MAP CARD (DROP (SUC h) As))` and scratch set `EL h As` in
its saved certificate. Thus a LIST_REL of independent existential d,A is
insufficient. These are proposed predecessor clauses, not proved invariants.

The required actual-rule budget conclusion is exactly:

    SUM (MAP CARD (A::As)) <= ctx_dload_count C

At a fresh configured scratch key q the required successor conclusion is:

    SUM (MAP CARD ((q INSERT A)::As)) <= ctx_dload_count C

The charging proof must derive, not assume, membership in a finite cap for the
actual frame's configured function. Existing ld_alloc_stack_budget consumes
function-indexed sets and source ld_stack_origin. An unresolved representation
choice is how to identify frame-indexed visited scratch sets with those
function-indexed sets while retaining the actual entry supply per frame.
`callee_first` excludes repeated functions along a live source stack, but
that source stack and its origins are outputs of the backward simulation;
the charging producer cannot assume an arbitrary source stack matching an
arbitrary target one. A target structural call-stack origin theorem or a
joint source/target stack-origin clause is necessary. Configured scratch IDs
cannot be inferred from source instruction IDs or a fixed arithmetic offset.
The strategist must choose this producer before authorizing a ledger proof.

At INVOKE push A into As and set child A={}, d'=d+32*CARD A. At return restore
the head's A and the tail-derived displacement. At a cached scratch leave A
unchanged. At a fresh scratch insert the configured generated ALLOCA ID,
charging its unique source DLOAD occurrence. The new budget plus source
headroom must derive t.vs_alloca_next+32 < dimword(:256); current nowrap alone
is inadequate. No new conditional arithmetic consumer is proposed here.

## Precise unresolved witness design

The synchronized source witness still has the E0093 source annotation
`ld_annotated_reachable vs C astk k L AP AG tn fn inst s` together with target
frame reachability, E, target ordinary map H, BP, AH, target mask un, and the
ledger above. The control component can now be written with actual prefix
and supply equations from active_origin and segment_index, instead of a
bracketed unspecified original-position relation. Strict prefixes retain the
entire pre-macro synchronized witness and ld_target_prefix, not an account
asserted at an intermediate state.

There is not yet an exact full HOL predicate: the unresolved choice is the
fixed-memory part of R and its relationship to clean non-pointer operands.
The proposed byte clause is

    ld_byte_rel R tn.t_mem un.t_mem
      (\j. read_memory j 1 s) (\j. read_memory j 1 t)

with every live owner's interval related and scratch excluded. To prove
ordinary raw-address loads/copies and to prove cached scratch separation,
R must also relate all legal fixed-region addresses by identity, with a
producer ensuring they avoid target scratch. Neither an arbitrary relation R
nor ld_frame_embedding implies this. An exact address-classification boundary
from source access_ok/raw_mem_ok is needed before installing this clause.
Do not assert all non-owner bytes correspond: those include scratch and dead
callee allocations. Naming an aggregate now would hide this design choice.

## Required producer/consumer map

1. Entry: same-state control theorem + relational PHI operand/taint theorem
   + initial empty owner/account/ledger. Must construct paired entry after
   actual lookup/setup, not assume related successor maps.
2. DLOAD: configured fresh/cached allocation account and four-phase prefix
   + successor reserve producer + cached scratch/live-byte separation
   + result value/provenance/taint-variable producer. Existing byte-completion
   theorem supplies only source step existence and memory correspondence.
   Generated variables must be excluded by actual supply freshness.
3. DLOADBYTES: pointer/size operand relation + destination relocation and
   payload byte relation, plus observation/taint update and control advance.
   It is not a scratch-only word-load theorem.
4. Ordinary instructions: source clean-control/ptr-use facts + classified
   operands + current memory/observation relation must produce an actual
   source step for a given target step, and preserve all witness clauses.
   Equal labels or entry on one state cannot produce operand definedness.
5. INVOKE: actual target decode, lookup, eval_operands, setup and entry must
   produce source counterparts; save parent certificate and cons the reserve
   chain. Clean INVOKE operands come from source taint discipline only after
   the paired operand theorem is available. Carry current shared memory,
   source stack origins, entry supplies and configured cap charging.
6. IntRet: actual target return must produce source IntRet and equal clean
   returned values (or an explicitly sufficient masked relation); then handle
   adopt_return_fmp and bind_outputs and caller PC. Restrict E only after
   proving all restored/current annotations survive. Saved-frame merge
   projections do not establish these facts; never restore saved memory.
7. External outcomes/nonmemory observations: specify compatible streams and
   source/target environmental fields before CALL or request proofs. The
   current annotations do not provide these clauses automatically.

All seven remain actual-rule preservation obligations, not hypotheses of the
final witness. A scoped PLAN must choose the reserve representation and
address-classification boundary before global execution induction.

## Final backward consumer, unchanged

Use taint_within_observation_transport in o1ContractLowerDloadTaintScript.sml,
lines 593-633. Its first premise demands a source request-producing ordinary
step for *every* reachable target request-producing ordinary step, with equal
call address, storage/transient dead-set agreement and mask inclusion. Its
second premise demands a source final_taint witness for every target final
observation, additionally immutable agreement, returndata agreement outside
D and taint/result-mask inclusion. The simultaneous witness must project both;
forward successful-run preservation alone proves neither quantifier pattern.
Source taint_within follows from o1_src_inv. No new premise may be added to
the frozen theorem to paper over reserve, related-state PHIs, clean operands,
scratch separation, outcome alignment, or rebinding.
