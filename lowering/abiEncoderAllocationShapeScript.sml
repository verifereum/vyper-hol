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

Theorem encoder_allocation_shape_mutual:
  (!dst src ei dyn off ptr sa.
    ci_mono sa (SND (compile_abi_encode_child dst src ei dyn off ptr sa)) /\
    EVERY (\i. i.inst_opcode = ALLOCA ==> i.inst_operands = [Lit 32w] /\
      ?q. i.inst_outputs = [q] /\ ~not_fresh_at sa q)
      (added_insts sa (SND (compile_abi_encode_child dst src ei dyn off ptr sa)))) /\
  (!dst src ei sa.
    ci_mono sa (SND (compile_abi_encode_to_buf dst src ei sa)) /\
    EVERY (\i. i.inst_opcode = ALLOCA ==> i.inst_operands = [Lit 32w] /\
      ?q. i.inst_outputs = [q] /\ ~not_fresh_at sa q)
      (added_insts sa (SND (compile_abi_encode_to_buf dst src ei sa)))) /\
  (!dst src infos so ho ptr sa.
    ci_mono sa (SND (compile_abi_encode_complex_elems dst src infos so ho ptr sa)) /\
    EVERY (\i. i.inst_opcode = ALLOCA ==> i.inst_operands = [Lit 32w] /\
      ?q. i.inst_outputs = [q] /\ ~not_fresh_at sa q)
      (added_insts sa (SND (compile_abi_encode_complex_elems dst src infos so ho ptr sa)))) /\
  (!dst src ei asz msz len sa.
    ci_mono sa (SND (compile_abi_encode_dyn_loop dst src ei asz msz len sa)) /\
    EVERY (\i. i.inst_opcode = ALLOCA ==> i.inst_operands = [Lit 32w] /\
      ?q. i.inst_outputs = [q] /\ ~not_fresh_at sa q)
      (added_insts sa (SND (compile_abi_encode_dyn_loop dst src ei asz msz len sa))))
Proof
  ho_match_mp_tac compile_abi_encode_child_ind >>
  rpt conj_tac
  >- suspend "child"
  >- suspend "word"
  >- suspend "bytes"
  >- suspend "copy"
  >- suspend "array"
  >- suspend "empty"
  >- suspend "complex"
  >- suspend "elems_nil"
  >- suspend "elems_cons"
  >> suspend "loop"
QED

Resume encoder_allocation_shape_mutual[child]:
  ntac 6 gen_tac >> strip_tac >> Cases_on `dyn` >> fs[] >>
  once_rewrite_tac[compile_abi_encode_child_def] >> simp_tac (srw_ss()) [] >>
  rpt (FIRST [
    (simp [added_insts_nonalloca_op_every, added_insts_nonalloca_void_every,
      added_insts_return_every] >> NO_TAC),
    ho_match_mp_tac added_insts_bind_relative_every >>
      (conj_tac >- metis_tac[allocation_shape_relative_mono]),
    ho_match_mp_tac added_insts_ignore_relative_every >>
      (conj_tac >- metis_tac[allocation_shape_relative_mono]),
    conj_tac, gen_tac])
QED

Resume encoder_allocation_shape_mutual[word]:
  simp[compile_abi_encode_child_def, encoder_static_allocation_shape]
QED

Resume encoder_allocation_shape_mutual[empty]:
  simp[compile_abi_encode_child_def, added_insts_return_every]
QED

Resume encoder_allocation_shape_mutual[elems_nil]:
  simp[compile_abi_encode_child_def, added_insts_return_every]
QED

Resume encoder_allocation_shape_mutual[copy]:
  ntac 3 gen_tac >> once_rewrite_tac[compile_abi_encode_child_def] >>
  ho_match_mp_tac added_insts_ignore_relative_every >>
  conj_tac >- metis_tac[allocation_shape_relative_mono] >>
  simp[added_insts_nonalloca_void_every, added_insts_return_every]
QED

Resume encoder_allocation_shape_mutual[bytes]:
  ntac 3 gen_tac >> once_rewrite_tac[compile_abi_encode_child_def] >>
  rpt (FIRST [
    (simp [added_insts_nonalloca_op_every, added_insts_nonalloca_void_every,
      added_insts_return_every] >> NO_TAC),
    ho_match_mp_tac added_insts_bind_relative_every >>
      (conj_tac >- metis_tac[allocation_shape_relative_mono]),
    ho_match_mp_tac added_insts_ignore_relative_every >>
      (conj_tac >- metis_tac[allocation_shape_relative_mono]),
    conj_tac, gen_tac])
QED

Resume encoder_allocation_shape_mutual[elems_cons]:
  rpt gen_tac >> strip_tac >>
  once_rewrite_tac[compile_abi_encode_child_def] >>
  rpt (FIRST [
    (simp [added_insts_nonalloca_op_every, added_insts_nonalloca_void_every,
      added_insts_return_every] >> NO_TAC),
    ho_match_mp_tac added_insts_bind_relative_every >>
      (conj_tac >- metis_tac[allocation_shape_relative_mono]),
    ho_match_mp_tac added_insts_ignore_relative_every >>
      (conj_tac >- metis_tac[allocation_shape_relative_mono]),
    conj_tac, gen_tac])
QED

Resume encoder_allocation_shape_mutual[loop]:
  rpt gen_tac >> strip_tac >>
  once_rewrite_tac[compile_abi_encode_child_def] >>
  simp_tac (srw_ss()) [LET_THM] >>
  rpt (FIRST [
    (simp [added_insts_allocate32_every, added_insts_nonalloca_op_every,
      added_insts_nonalloca_void_every, added_insts_nonalloca_inst_every,
      added_insts_fresh_label_every, added_insts_new_block_every,
      added_insts_return_every] >> NO_TAC),
    ho_match_mp_tac added_insts_bind_relative_every >>
      (conj_tac >- metis_tac[allocation_shape_relative_mono]),
    ho_match_mp_tac added_insts_ignore_relative_every >>
      (conj_tac >- metis_tac[allocation_shape_relative_mono]),
    conj_tac, gen_tac])
QED

Resume encoder_allocation_shape_mutual[array]:
  rpt gen_tac >> strip_tac >> Cases_on `elem_is_dyn` >> fs[] >>
  once_rewrite_tac[compile_abi_encode_child_def] >>
  simp_tac (srw_ss()) [LET_THM] >>
  rpt (FIRST [
    (simp [added_insts_allocate32_every, added_insts_nonalloca_op_every,
      added_insts_nonalloca_void_every, added_insts_return_every,
      encoder_static_loop_allocation_shape] >> NO_TAC),
    ho_match_mp_tac added_insts_bind_relative_every >>
      (conj_tac >- metis_tac[allocation_shape_relative_mono]),
    ho_match_mp_tac added_insts_ignore_relative_every >>
      (conj_tac >- metis_tac[allocation_shape_relative_mono]),
    conj_tac, gen_tac])
QED

Resume encoder_allocation_shape_mutual[complex]:
  rpt gen_tac >> strip_tac >>
  once_rewrite_tac[compile_abi_encode_child_def] >>
  simp_tac (srw_ss()) [LET_THM] >>
  IF_CASES_TAC >> fs[] >>
  rpt (FIRST [
    (simp [added_insts_allocate32_every, added_insts_nonalloca_op_every,
      added_insts_nonalloca_void_every, added_insts_return_every] >> NO_TAC),
    ho_match_mp_tac added_insts_bind_relative_every >>
      (conj_tac >- metis_tac[allocation_shape_relative_mono]),
    ho_match_mp_tac added_insts_ignore_relative_every >>
      (conj_tac >- metis_tac[allocation_shape_relative_mono]),
    conj_tac, gen_tac])
QED

Finalise encoder_allocation_shape_mutual

Theorem encoder_to_buf_allocation_shape:
  !dst src ei sa.
    ci_mono sa (SND (compile_abi_encode_to_buf dst src ei sa)) /\
    EVERY (\i. i.inst_opcode = ALLOCA ==> i.inst_operands = [Lit 32w] /\
      ?q. i.inst_outputs = [q] /\ ~not_fresh_at sa q)
      (added_insts sa (SND (compile_abi_encode_to_buf dst src ei sa)))
Proof
  metis_tac[encoder_allocation_shape_mutual]
QED

Theorem encoder_id_coverage_mutual:
  (!dst src ei dyn off ptr sa.
    ci_mono sa (SND (compile_abi_encode_child dst src ei dyn off ptr sa)) /\
    !id. id IN frag_ids sa (SND (compile_abi_encode_child dst src ei dyn off ptr sa)) ==>
      ?i. MEM i (added_insts sa (SND (compile_abi_encode_child dst src ei dyn off ptr sa))) /\ i.inst_id = id) /\
  (!dst src ei sa.
    ci_mono sa (SND (compile_abi_encode_to_buf dst src ei sa)) /\
    !id. id IN frag_ids sa (SND (compile_abi_encode_to_buf dst src ei sa)) ==>
      ?i. MEM i (added_insts sa (SND (compile_abi_encode_to_buf dst src ei sa))) /\ i.inst_id = id) /\
  (!dst src infos so ho ptr sa.
    ci_mono sa (SND (compile_abi_encode_complex_elems dst src infos so ho ptr sa)) /\
    !id. id IN frag_ids sa (SND (compile_abi_encode_complex_elems dst src infos so ho ptr sa)) ==>
      ?i. MEM i (added_insts sa (SND (compile_abi_encode_complex_elems dst src infos so ho ptr sa))) /\ i.inst_id = id) /\
  (!dst src ei asz msz len sa.
    ci_mono sa (SND (compile_abi_encode_dyn_loop dst src ei asz msz len sa)) /\
    !id. id IN frag_ids sa (SND (compile_abi_encode_dyn_loop dst src ei asz msz len sa)) ==>
      ?i. MEM i (added_insts sa (SND (compile_abi_encode_dyn_loop dst src ei asz msz len sa))) /\ i.inst_id = id)
Proof
  ho_match_mp_tac compile_abi_encode_child_ind >>
  rpt conj_tac
  >- suspend "child"
  >- suspend "word"
  >- suspend "bytes"
  >- suspend "copy"
  >- suspend "array"
  >- suspend "empty"
  >- suspend "complex"
  >- suspend "elems_nil"
  >- suspend "elems_cons"
  >> suspend "loop"
QED

Resume encoder_id_coverage_mutual[child]:
  ntac 6 gen_tac >> strip_tac >> Cases_on `dyn` >> fs[] >>
  once_rewrite_tac[compile_abi_encode_child_def] >> simp_tac (srw_ss()) [] >>
  rpt (FIRST [
    (simp [added_insts_emit_op_coverage, added_insts_emit_void_coverage,
      added_insts_return_coverage] >> NO_TAC),
    ho_match_mp_tac added_insts_bind_coverage,
    ho_match_mp_tac added_insts_ignore_coverage,
    conj_tac, gen_tac])
QED

Resume encoder_id_coverage_mutual[word]:
  simp[compile_abi_encode_child_def, encoder_static_id_coverage]
QED

Resume encoder_id_coverage_mutual[empty]:
  simp[compile_abi_encode_child_def, added_insts_return_coverage]
QED

Resume encoder_id_coverage_mutual[elems_nil]:
  simp[compile_abi_encode_child_def, added_insts_return_coverage]
QED

Resume encoder_id_coverage_mutual[copy]:
  ntac 3 gen_tac >> once_rewrite_tac[compile_abi_encode_child_def] >>
  ho_match_mp_tac added_insts_ignore_coverage >>
  simp[added_insts_emit_void_coverage, added_insts_return_coverage]
QED

Resume encoder_id_coverage_mutual[bytes]:
  ntac 3 gen_tac >> once_rewrite_tac[compile_abi_encode_child_def] >>
  rpt (FIRST [
    (simp [added_insts_emit_op_coverage, added_insts_emit_void_coverage,
      added_insts_return_coverage] >> NO_TAC),
    ho_match_mp_tac added_insts_bind_coverage,
    ho_match_mp_tac added_insts_ignore_coverage,
    conj_tac, gen_tac])
QED

Resume encoder_id_coverage_mutual[elems_cons]:
  rpt gen_tac >> strip_tac >>
  once_rewrite_tac[compile_abi_encode_child_def] >>
  rpt (FIRST [
    (simp [added_insts_emit_op_coverage, added_insts_emit_void_coverage,
      added_insts_return_coverage] >> NO_TAC),
    ho_match_mp_tac added_insts_bind_coverage,
    ho_match_mp_tac added_insts_ignore_coverage,
    conj_tac, gen_tac])
QED

Resume encoder_id_coverage_mutual[loop]:
  rpt gen_tac >> strip_tac >>
  once_rewrite_tac[compile_abi_encode_child_def] >>
  simp_tac (srw_ss()) [LET_THM] >>
  rpt (FIRST [
    (simp [added_insts_allocate_coverage, added_insts_emit_op_coverage,
      added_insts_emit_void_coverage, added_insts_emit_inst_coverage,
      added_insts_fresh_label_coverage, added_insts_new_block_coverage,
      added_insts_return_coverage] >> NO_TAC),
    ho_match_mp_tac added_insts_bind_coverage,
    ho_match_mp_tac added_insts_ignore_coverage,
    conj_tac, gen_tac])
QED

Resume encoder_id_coverage_mutual[array]:
  rpt gen_tac >> strip_tac >> Cases_on `elem_is_dyn` >> fs[] >>
  once_rewrite_tac[compile_abi_encode_child_def] >>
  simp_tac (srw_ss()) [LET_THM] >>
  rpt (FIRST [
    (simp [added_insts_allocate_coverage, added_insts_emit_op_coverage,
      added_insts_emit_void_coverage, added_insts_return_coverage,
      encoder_static_loop_id_coverage] >> NO_TAC),
    ho_match_mp_tac added_insts_bind_coverage,
    ho_match_mp_tac added_insts_ignore_coverage,
    conj_tac, gen_tac])
QED

Resume encoder_id_coverage_mutual[complex]:
  rpt gen_tac >> strip_tac >>
  once_rewrite_tac[compile_abi_encode_child_def] >>
  simp_tac (srw_ss()) [LET_THM] >>
  IF_CASES_TAC >> fs[] >>
  rpt (FIRST [
    (simp [added_insts_allocate_coverage, added_insts_emit_op_coverage,
      added_insts_emit_void_coverage, added_insts_return_coverage] >> NO_TAC),
    ho_match_mp_tac added_insts_bind_coverage,
    ho_match_mp_tac added_insts_ignore_coverage,
    conj_tac, gen_tac])
QED

Finalise encoder_id_coverage_mutual

Theorem encoder_to_buf_id_coverage:
  !dst src ei sa.
    ci_mono sa (SND (compile_abi_encode_to_buf dst src ei sa)) /\
    !id. id IN frag_ids sa (SND (compile_abi_encode_to_buf dst src ei sa)) ==>
      ?i. MEM i (added_insts sa (SND (compile_abi_encode_to_buf dst src ei sa))) /\ i.inst_id = id
Proof
  metis_tac[encoder_id_coverage_mutual]
QED
