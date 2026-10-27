# Encoder shared-runner ownership proposal (C1.B.A)

**For owner decision, not authorization to edit #762.** No established theory
has been edited for this proposal. The frozen theorem remains unresolved;
no execution counterexample has been established. A thin adapter is insufficient:
the checked same-shape cardinality obstruction defeats the old input interface,
and reserve framing does not imply registered-slot framing.

## Exact proposed shared runner interface

Add `abi_encoder_shared_runner ei` with the following defining RHS. This is a
proposal only, not a new axiom or a claim that the theorem is already proved.
All physical resource, PHI and entry premises of `abi_scratch_encoder` remain.
Only the input relation changes, and the postcondition gains a conjunct at the
**same** existential state:

```sml
!dst src start end_st out func ctx first last b cap limit_st initial
  at av sb source_cap d.
  compile_abi_encode_to_buf dst src ei start = (out,end_st) /\
  fn_has_code start end_st func /\
  (start.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_encoder_open_input ei at av sb source_cap initial.vs_memory /\
  eval_operand src initial = SOME (n2w sb) /\
  eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live start.cs_next_var src /\
  abi_decoder_operand_live start.cs_next_var dst /\
  sb+source_cap < dimword (:256) /\
  d+LENGTH (enc at av) < dimword (:256) /\
  (sb+source_cap <= d \/ d+LENGTH (enc at av) <= sb) /\
  abi_footprint_disjoint sb source_cap
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) /\
  abi_footprint_disjoint d (LENGTH (enc at av))
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) /\
  abi_decoder_budget first last b cap initial /\
  first <= start.cs_next_id /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual.
    mem_bytes_at d (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    eval_operand out actual = SOME (n2w (LENGTH (enc at av))) /\
    abi_scratch_effect first last start.cs_next_id end_st.cs_next_id
      start.cs_next_var limit_st d (LENGTH (enc at av)) b cap initial actual /\
    abi_encoder_registered_effect (abi_decoder_ids start.cs_next_id end_st.cs_next_id)
      [(d,LENGTH (enc at av))] initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
```

Old `abi_scratch_encoder` follows by `abi_encoder_input_open` and projection;
its definition and all existing theorem statements can remain unchanged.
The new derivation must replace/factor existing proof bodies, not coexist with
an independent recursive execution proof. This requires owner approval under
the task's preservation/ownership constraints.

## Minimal factoring sites (not an exhaustive rewrite)

* **Leaves:** `abiScratchEncoderLeaves` word/copy/bytes theorems use the
  existing sequence/reentry executions. Factor their input elimination and
  `abiScratchLeafEffect.abi_scratch_leaf_reach` post assembly so that the
  output-only frame and unchanged allocations also give registered effects.
  No new recursive argument here; keep the very same sequence endpoint.
* **Complex/member recursion:** `abiScratchComplex` prepare/compose/finish,
  `abiScratchMembersCorrect` cons, and
  `abiScratchMembersAdvance.abi_scratch_members_child_advance` are the spine.
  Add parallel open-input/member invariants and a shared member-runner
  interface at `abiScratchMembers`'s correct/run boundary (lines 305–368).
  Factor the existing cons derivation to thread both effects through prepare,
  child and tail. The owned range must begin at the parent's `lo`, not the
  child's `st.cs_next_id`: parent cursor writes precede the child interval.
* **Arrays:** `abiScratchArrayParent` prepare/finish and
  `abiScratchArrayRun` parent_prepare/selected_loop/finish_protected carry
  the shared endpoint. Add registered-effect accumulation to the loop
  invariant and factor `abiScratchArrayFiniteLoop` dynamic_step/exit/
  dynamic_finite_loop (lines 11–101), through
  `abiScratchArrayDynamicRound` and the child execution boundary.
  Retain `valid_length NONE avs`; removing outer complex cardinality does
  not justify an unrepresentable runtime loop count.
* **Allocation/write primitives:** reuse actual slot-allocation executions
  called by those prepare/header/round sites. At each allocation plus cursor
  store, prove registered preservation from the actual allocation record;
  compose with `abi_encoder_registered_effect_trans` and enlarge owned IDs
  explicitly. Physical `abi_scratch_effect_widen` alone cannot do this.
* **Closure:** factor `abiScratchEncoderRecursive`'s existing admissible
  mutual induction (lines 9–18) to prove the shared runner. Export the old
  closure by projection, preserving its name and statement. Constructors
  must consume shared child runners, never two existential runs.

## Remaining gates, deliberately not hidden by this proposal

Open input alone does not solve universal source production: its copy/word
leaves retain `has_type`. Giant zero-size static tuple copies still need an
encoding-equivalent leaf representative (or another approved interface).
Separately derive physical budgets/disjointness, PHI conditions, scratch-count
bounds, and variable restoration from the frozen premises; then identify
`abi_decoder_ids` with `frag_ids` and apply registered_effect_frame at that
same endpoint. These are unproved obligations, not extra public hypotheses.
The proposal selects the runner boundary, not a proof of these bridges.

## Audit scope

`abiEncoderReuseAudit` checks eight named propagated proof-oracle tags,
including the scratch admissible closure/translation and selected new pure
boundaries. It rejects CHEAT and other non-DISK_THM tags. Loaded `.dat` files
lose upstream axiom dependencies: `null Tag.axioms` is **not** an upstream
axiom-freedom audit. Such a claim would require source auditing. Neither a
successful build nor importing a legacy admitted ancestor proves use of its
admitted theorem. No complete transitive source axiom audit is claimed here.

**Decision requested:** may the existing constructor/member/array proof bodies
and recursive closure be factored as above, preserving every established
statement/definition, with one shared derivation and old-contract corollaries?
Until an explicit owner decision, do not edit #762 or begin universal recursion.
