(* Pointer navigation preserves the workspace needed by recursive decoding. *)
Theory abiDecoderReservation
Ancestors
  abiDecoderTypedContract abiDecoderCoherence abiDecoderContract abiDecoderFrame
  abiEncoder emitHelper exprLoweringProps compileEnv venomMemProps
  venomExecSemantics venomState venomInst words list rich_list arithmetic

Theorem abi_decode_sequence_allocation_frame:
  !insts s t.
  EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode) insts /\
  run_inst_seq insts s = OK t ==>
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  Induct >> simp[run_inst_seq_def] >> qx_gen_tac `inst` >> rpt gen_tac >> strip_tac >>
  Cases_on `step_inst_base inst s` >> gvs[] >>
  drule_all step_inst_base_preserves_alloca_state >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem abi_decoder_reservation_advance:
  abi_decoder_reservation first last b cap s /\ first <= next /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next ==>
  abi_decoder_reservation next last b cap t
Proof
  rw[abi_decoder_reservation_def] >>
  `first <= id` by decide_tac >> first_x_assum drule_all >> simp[]
QED

Theorem abi_decoder_ranges_pure_transport:
  abi_decoder_ranges opc hi src dst sb len d outsz b cap s /\
  (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) ==>
  abi_decoder_ranges opc hi src dst sb len d outsz b cap t
Proof
  rw[abi_decoder_ranges_def] >> metis_tac[]
QED

Theorem abi_decoder_pre_pure_transport:
  abi_decoder_pre ce env ty tv di av v st last src dst opc hi sb d b cap s /\
  st.cs_next_id <= st'.cs_next_id /\ fresh_vars_wrt st' t /\
  (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
  t.vs_data_section = s.vs_data_section ==>
  abi_decoder_pre ce env ty tv di av v st' last src dst opc hi sb d b cap t
Proof
  strip_tac >>
  qpat_x_assum `abi_decoder_pre ce env ty tv di av v st last src dst opc hi sb d b cap s`
    mp_tac >> simp_tac bool_ss [abi_decoder_pre_def] >> strip_tac >>
  drule_all abi_decoder_reservation_advance >> strip_tac >>
  drule_all abi_decoder_ranges_pure_transport >> strip_tac >>
  gvs[abi_decode_source_def]
QED

Theorem abi_decoder_source_frame:
  abi_decoder_ranges opc hi src dst sb len d outsz b cap s /\
  abi_decode_footprint_frame [(d,outsz);(b,cap)] s t ==>
  mem_bytes_at sb len (abi_decode_source opc t) =
    mem_bytes_at sb len (abi_decode_source opc s)
Proof
  rw[abi_decoder_ranges_def, abi_decode_source_opcode_def,
     abi_decode_source_def, abi_decode_footprint_frame_def] >>
  first_x_assum irule >> first_assum ACCEPT_TAC
QED

Theorem abi_decoder_pre_transport:
  abi_decoder_pre ce env ty tv di av v st last src dst opc hi sb d b cap s /\
  abi_decoder_reservation st'.cs_next_id last b cap t /\ fresh_vars_wrt st' t /\
  (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
  abi_decode_footprint_frame [(d,type_memory_bytes ce ty);(b,cap)] s t ==>
  abi_decoder_pre ce env ty tv di av v st' last src dst opc hi sb d b cap t
Proof
  strip_tac >>
  qpat_x_assum `abi_decoder_pre ce env ty tv di av v st last src dst opc hi sb d b cap s`
    mp_tac >> simp_tac bool_ss [abi_decoder_pre_def] >> strip_tac >>
  drule_all abi_decoder_ranges_pure_transport >> strip_tac >>
  drule_all abi_decoder_source_frame >> strip_tac >> gvs[]
QED

Theorem abi_decoder_recursive_pre_transport:
  abi_decoder_recursive_pre ce env sf ty tv di av v st last src dst opc hi sb d b cap s /\
  abi_decoder_reservation st'.cs_next_id last b cap t /\ fresh_vars_wrt st' t /\
  (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
  abi_decode_footprint_frame [(d,type_memory_bytes ce ty);(b,cap)] s t ==>
  abi_decoder_recursive_pre ce env sf ty tv di av v st' last src dst opc hi sb d b cap t
Proof
  rw[abi_decoder_recursive_pre_def] >> drule_all abi_decoder_pre_transport >> simp[]
QED

Theorem abi_decoder_recursive_pre_pure_transport:
  abi_decoder_recursive_pre ce env sf ty tv di av v st last src dst opc hi sb d b cap s /\
  st.cs_next_id <= st'.cs_next_id /\ fresh_vars_wrt st' t /\
  (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
  t.vs_data_section = s.vs_data_section ==>
  abi_decoder_recursive_pre ce env sf ty tv di av v st' last src dst opc hi sb d b cap t
Proof
  rw[abi_decoder_recursive_pre_def] >>
  drule_all abi_decoder_pre_pure_transport >> simp[]
QED

Theorem abi_decode_member_pointer_allocation_shape:
  compile_getelemptr_abi src is_dyn off opc hi st = (member_op,st') /\
  (is_dyn ==> abi_decode_source_opcode opc) ==>
  st.cs_next_id <= st'.cs_next_id /\
  EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
    (emitted_insts st st')
Proof
  strip_tac >> Cases_on `is_dyn` >> gvs[abi_decode_source_opcode_def] >>
  Cases_on `hi = Lit 0w` >>
  gvs[compile_getelemptr_abi_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
      fresh_id_def, emit_def, emitted_insts_def] >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
  gvs[DROP_LENGTH_APPEND, is_terminator_def, is_alloca_op_def, mk_inst_def]
QED

Theorem abi_decode_array_pointer_allocation_shape:
  compile_abi_decode_dyn_elem_ptr opc elem_src src_data hi abi_sz st = (child_op,st') /\
  abi_decode_source_opcode opc ==>
  st.cs_next_id <= st'.cs_next_id /\
  EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
    (emitted_insts st st')
Proof
  strip_tac >> gvs[abi_decode_source_opcode_def] >> Cases_on `hi = Lit 0w` >>
  gvs[compile_abi_decode_dyn_elem_ptr_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
      fresh_id_def, emit_def, emitted_insts_def] >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
  gvs[DROP_LENGTH_APPEND, is_terminator_def, is_alloca_op_def, mk_inst_def]
QED

Theorem abi_decode_member_pointer_reservation:
  compile_getelemptr_abi src is_dyn off opc hi st = (member_op,st') /\
  (is_dyn ==> abi_decode_source_opcode opc) /\
  run_inst_seq (emitted_insts st st') s = OK t /\
  abi_decoder_reservation st.cs_next_id last b cap s ==>
  abi_decoder_reservation st'.cs_next_id last b cap t
Proof
  strip_tac >> drule_all abi_decode_member_pointer_allocation_shape >> strip_tac >>
  drule_all abi_decode_sequence_allocation_frame >> strip_tac >>
  drule_all abi_decoder_reservation_advance >> simp[]
QED

Theorem abi_decode_array_pointer_reservation:
  compile_abi_decode_dyn_elem_ptr opc elem_src src_data hi abi_sz st = (child_op,st') /\
  abi_decode_source_opcode opc /\
  run_inst_seq (emitted_insts st st') s = OK t /\
  abi_decoder_reservation st.cs_next_id last b cap s ==>
  abi_decoder_reservation st'.cs_next_id last b cap t
Proof
  strip_tac >> drule_all abi_decode_array_pointer_allocation_shape >> strip_tac >>
  drule_all abi_decode_sequence_allocation_frame >> strip_tac >>
  drule_all abi_decoder_reservation_advance >> simp[]
QED
