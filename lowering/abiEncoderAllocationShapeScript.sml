(* Syntactic allocation shape of encoder instruction suffixes. *)
Theory abiEncoderAllocationShape
Ancestors
  compilerInstructionSuffix abiEncoder loweringShapeDefs compileEnv context
  emitHelper exprLoweringProps list venomInst

Theorem encoder_static_allocation_shape:
  !dst src sa.
  ci_mono sa (SND (compile_abi_encode_static dst src sa)) /\
  EVERY (\i. i.inst_opcode = ALLOCA ==> i.inst_operands = [Lit 32w] /\
    ?q. i.inst_outputs = [q] /\ ~not_fresh_at sa q)
    (added_insts sa (SND (compile_abi_encode_static dst src sa)))
Proof
  ntac 2 gen_tac >> simp[compile_abi_encode_static_def] >>
  ho_match_mp_tac added_insts_bind_relative_every >>
  conj_tac >- metis_tac[allocation_shape_relative_mono] >>
  conj_tac >- simp[added_insts_nonalloca_op_every] >>
  gen_tac >> ho_match_mp_tac added_insts_ignore_relative_every >>
  conj_tac >- metis_tac[allocation_shape_relative_mono] >>
  simp[added_insts_nonalloca_void_every, added_insts_return_every]
QED

Theorem encoder_static_info_allocation_shape:
  !dst src info sa.
  ci_mono sa (SND (compile_abi_encode_static_info dst src info sa)) /\
  EVERY (\i. i.inst_opcode = ALLOCA ==> i.inst_operands = [Lit 32w] /\
    ?q. i.inst_outputs = [q] /\ ~not_fresh_at sa q)
    (added_insts sa (SND (compile_abi_encode_static_info dst src info sa)))
Proof
  ntac 3 gen_tac >> Cases_on `info` >>
  simp[compile_abi_encode_static_info_def, encoder_static_allocation_shape,
       added_insts_return_every] >>
  ho_match_mp_tac added_insts_ignore_relative_every >>
  conj_tac >- metis_tac[allocation_shape_relative_mono] >>
  simp[added_insts_nonalloca_void_every, added_insts_return_every]
QED

Theorem encoder_static_loop_allocation_shape:
  !dst src info asz msz len sa.
  ci_mono sa (SND (compile_abi_encode_dyn_static_loop dst src info asz msz len sa)) /\
  EVERY (\i. i.inst_opcode = ALLOCA ==> i.inst_operands = [Lit 32w] /\
    ?q. i.inst_outputs = [q] /\ ~not_fresh_at sa q)
    (added_insts sa (SND (compile_abi_encode_dyn_static_loop dst src info asz msz len sa)))
Proof
  ntac 6 gen_tac >> simp[compile_abi_encode_dyn_static_loop_def] >>
  rpt (FIRST [
    (simp [added_insts_allocate32_every, added_insts_nonalloca_op_every,
      added_insts_nonalloca_void_every, added_insts_nonalloca_inst_every,
      added_insts_fresh_label_every, added_insts_new_block_every,
      added_insts_return_every, encoder_static_info_allocation_shape] >> NO_TAC),
    ho_match_mp_tac added_insts_bind_relative_every >>
      (conj_tac >- metis_tac[allocation_shape_relative_mono]),
    ho_match_mp_tac added_insts_ignore_relative_every >>
      (conj_tac >- metis_tac[allocation_shape_relative_mono]),
    conj_tac, gen_tac])
QED

Theorem encoder_static_id_coverage:
  !dst src sa.
  ci_mono sa (SND (compile_abi_encode_static dst src sa)) /\
  !id. id IN frag_ids sa (SND (compile_abi_encode_static dst src sa)) ==>
    ?i. MEM i (added_insts sa (SND (compile_abi_encode_static dst src sa))) /\
        i.inst_id = id
Proof
  ntac 2 gen_tac >> simp[compile_abi_encode_static_def] >>
  ho_match_mp_tac added_insts_bind_coverage >>
  conj_tac >- simp[added_insts_emit_op_coverage] >>
  gen_tac >> ho_match_mp_tac added_insts_ignore_coverage >>
  simp[added_insts_emit_void_coverage, added_insts_return_coverage]
QED

Theorem encoder_static_info_id_coverage:
  !dst src info sa.
  ci_mono sa (SND (compile_abi_encode_static_info dst src info sa)) /\
  !id. id IN frag_ids sa (SND (compile_abi_encode_static_info dst src info sa)) ==>
    ?i. MEM i (added_insts sa (SND (compile_abi_encode_static_info dst src info sa))) /\
        i.inst_id = id
Proof
  ntac 3 gen_tac >> Cases_on `info` >>
  simp[compile_abi_encode_static_info_def, encoder_static_id_coverage,
       added_insts_return_coverage] >>
  ho_match_mp_tac added_insts_ignore_coverage >>
  simp[added_insts_emit_void_coverage, added_insts_return_coverage]
QED

Theorem encoder_static_loop_id_coverage:
  !dst src info asz msz len sa.
  ci_mono sa (SND (compile_abi_encode_dyn_static_loop dst src info asz msz len sa)) /\
  !id. id IN frag_ids sa
      (SND (compile_abi_encode_dyn_static_loop dst src info asz msz len sa)) ==>
    ?i. MEM i (added_insts sa
      (SND (compile_abi_encode_dyn_static_loop dst src info asz msz len sa))) /\
      i.inst_id = id
Proof
  ntac 6 gen_tac >> simp[compile_abi_encode_dyn_static_loop_def] >>
  rpt (FIRST [
    (simp [added_insts_allocate_coverage, added_insts_emit_op_coverage,
      added_insts_emit_void_coverage, added_insts_emit_inst_coverage,
      added_insts_fresh_label_coverage, added_insts_new_block_coverage,
      added_insts_return_coverage, encoder_static_info_id_coverage] >> NO_TAC),
    ho_match_mp_tac added_insts_bind_coverage,
    ho_match_mp_tac added_insts_ignore_coverage,
    conj_tac, gen_tac])
QED
