Theory dftPositionalFallibleOrder
Ancestors
  dftPositionalProvenance dftPositionalSchedule dftRunRel dftSsaPreserve dftScheduleOrder
  dftDefs venomInst venomEffects opcodeClass list

Theorem dft_inversion_abort_compatible:
  ALL_DISTINCT (MAP (\i. i.inst_id) dst) /\
  id_before src x y /\ id_before dst y x /\
  (!a b. MEM a src /\ MEM b src /\
    ~abort_compatible a.inst_opcode b.inst_opcode /\
    id_before (MAP (\i. i.inst_id) src) a.inst_id b.inst_id ==>
    id_before (MAP (\i. i.inst_id) dst) a.inst_id b.inst_id) ==>
  abort_compatible x.inst_opcode y.inst_opcode
Proof
  strip_tac >> spose_not_then assume_tac >>
  `MEM x src /\ MEM y src` by metis_tac[id_before_mem] >>
  `id_before (MAP (\i. i.inst_id) src) x.inst_id y.inst_id` by
    metis_tac[dftSsaPreserveTheory.id_before_map] >>
  `id_before (MAP (\i. i.inst_id) dst) y.inst_id x.inst_id` by
    metis_tac[dftSsaPreserveTheory.id_before_map] >>
  metis_tac[id_before_asym]
QED

Theorem dft_pos_guard_abort_compatible:
  dft_fallible_order_kept f g /\ k < LENGTH f.fn_blocks /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (EL k g.fn_blocks).bb_instructions) /\
  dft_pos_schedule_guard (EL k f.fn_blocks) (EL k g.fn_blocks)
    R fi bi pre x y post ==>
  abort_compatible x.inst_opcode y.inst_opcode
Proof
  simp[dft_fallible_order_kept_def, LIST_REL_EL_EQN,
       dft_pos_schedule_guard_def] >> strip_tac >>
  irule dft_inversion_abort_compatible >>
  qexistsl [`(EL k g.fn_blocks).bb_instructions`,
             `(EL k f.fn_blocks).bb_instructions`] >> simp[]
QED

Theorem dft_invoke_compatible_fail_class:
  abort_compatible op INVOKE ==>
  opcode_fail_class op = NoFail \/ opcode_fail_class op = AnyFail
Proof
  simp[abort_compatible_def, opcode_fail_class_def]
QED

Theorem dft_invoke_compatible_noninvoke:
  abort_compatible op INVOKE /\ op <> INVOKE ==>
  opcode_fail_class op = NoFail
Proof
  Cases_on `op` >> simp[abort_compatible_def, opcode_fail_class_def]
QED

Theorem dft_invoke_assert_incompatible:
  ~abort_compatible ASSERT INVOKE /\
  ~abort_compatible ASSERT_UNREACHABLE INVOKE
Proof
  simp[abort_compatible_def, opcode_fail_class_def]
QED

(* Producer/consumer audit (endpoint obligations are not assumed discharged):
   - dft_fn_rel_def contains dft_fallible_order_kept for the final function.
     LIST_REL_EL_EQN exposes it for each pair in the compiler premise.
   - dft_block_rel_guarded_reconstruction (dftFlipRuntime) produces an
     original-block permutation mid, with LIST_REL flip_rel mid dest.
     dft_original_block_perm plus wf_fn_block_inst_ids_distinct supply
     distinct IDs for mid. Its conclusion does NOT export fallible order
     from the original block to mid.
   - dft_pos_provenance_factor constructs the path to Cdest assuming
     original-context and schedule_edges. No fallible-order premise occurs.
     There are currently no external callers of that factor theorem.
   - dft_pos_provenance_guard retains original/destination inversions;
     dft_pos_provenance_edge_extract discards those inversion facts.
     The boundary above therefore consumes the guard, not the extraction.
   - dft_crossing_evidence_def requires an explicit OK partner step; neither
     the positional factor nor abort compatibility constructs that witness.

   Missing normalization bridge: transport ID-order preservation from the
   final output to the reconstructed mid along LIST_REL flip_rel, lifting
   this blockwise through function/context reconstruction. Flips preserve
   IDs (flip_operands_inst_id) but not opcode equality (comparators change).
   A fail-class preservation boundary, rather than unconditional opcode
   preservation, is appropriate if compatibility is transported as well.
   No reconstructed context-to-positional-path producer currently supplies
   these combined endpoint premises. No reverse execution integration is
   claimed here. NoFail still permits Error and does not imply OK.
*)
