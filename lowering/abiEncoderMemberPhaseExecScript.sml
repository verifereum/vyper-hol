(* Concrete endpoints, independent of the invariant transported by a member. *)
Theory abiEncoderMemberPhaseExec
Ancestors
  abiScratchMembers abiScratchAddress abiScratchChild abiScratchEncoderContract
  abiEncoderChildSuffix abiDecoderFrame
  abiEncoderMembersContract abiEncoderMembersDefs abiEncoderMembersSource
  abiEncoderTuple abiEncoderChildInputs abiEncoderInput abiCanonicalWindows
  abiDecoderArrayInitExec abiDecoderLoop emitHelperProps valueEncoding arithmetic
  abiEncoderAddressReach abiDecoderReentryAddress abiDecoderDynamicLoopSetup
  abiDecoderReentry abiDecoderContract fragExec compileEnv venomState
  venomExecSemantics instIdxIndep words list

Definition abi_encoder_member_phase_raw_def:
  abi_encoder_member_phase_raw st final initial ready <=>
    ?u. run_inst_seq (emitted_insts st final) initial = OK u /\
        ready = (u with vs_inst_idx := LENGTH final.cs_current_insts)
End

Theorem abi_encoder_member_binary_raw:
  emit_op opc [lhs;rhs] st = (out,final) /\ (opc = ADD \/ opc = MUL) /\
  eval_operand lhs initial = SOME a /\ eval_operand rhs initial = SOME b /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?ready. abi_encoder_member_phase_raw st final initial ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_binary_reentry >> strip_tac >>
  qexists_tac `t with vs_inst_idx := LENGTH final.cs_current_insts` >>
  simp[abi_encoder_member_phase_raw_def] >> qexists_tac `t` >> simp[]
QED

Theorem abi_encoder_member_binary_transport:
  emit_op opc [lhs;rhs] st = (out,final) /\ (opc = ADD \/ opc = MUL) /\
  eval_operand lhs initial = SOME a /\ eval_operand rhs initial = SOME b /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_encoder_member_phase_raw st final initial ready ==>
  eval_operand out ready = SOME (if opc = ADD then a+b else a*b) /\
  fresh_vars_wrt limit_st ready /\ abi_decoder_address_frame st.cs_next_var initial ready /\
  ready.vs_current_bb = initial.vs_current_bb /\
  ready.vs_inst_idx = LENGTH final.cs_current_insts /\
  ready.vs_halted = initial.vs_halted
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_binary_reentry >> strip_tac >>
  gvs[abi_encoder_member_phase_raw_def] >>
  gvs[abi_decoder_address_frame_def, fresh_vars_wrt_def, eval_op_inst_idx,
      update_var_def]
QED

Theorem abi_encoder_members_prepare_raw_transport:
  emit_op ADD [src;Lit (n2w so)] st = (elem_src,prepared) /\
  abi_encoder_members_inv ((ei,abi_sz,mem_sz,dyn)::infos) (ty::tys) (av::avs)
    pre pvs active dyn_ptr site slot first last lo st limit_st
    src dst sb so ho d hl output_size b cap initial /\
  prepared.cs_next_var <= limit_st.cs_next_var /\
  abi_encoder_member_phase_raw st prepared initial ready ==>
  abi_encoder_members_inv ((ei,abi_sz,mem_sz,dyn)::infos) (ty::tys) (av::avs)
    pre pvs active dyn_ptr site slot first last lo prepared limit_st
    src dst sb so ho d hl output_size b cap ready /\
  abi_encoder_buffer_pre ei ty av prepared elem_src dst (sb+so) mem_sz d output_size b cap ready /\
  abi_decoder_address_frame st.cs_next_var initial ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_members_inv_def]) >>
  qpat_assum `abi_encoder_members_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_members_pre_def]) >>
  drule abi_encoder_emit_address_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >> drule abi_decoder_operand_live_emit >> strip_tac >>
  `st.cs_next_var <= prepared.cs_next_var /\ st.cs_next_id <= prepared.cs_next_id` by decide_tac >>
  `eval_operand (Lit (n2w so)) initial = SOME (n2w so)` by simp[eval_operand_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`] abi_encoder_member_binary_transport)) >> strip_tac >>
  `eval_operand elem_src ready = SOME (n2w (sb+so))` by fs[word_add_n2w] >>
  mp_tac (Q.INST [`actual` |-> `ready:venom_state`, `infos` |-> `(ei,abi_sz,mem_sz,dyn)::infos`,
    `tys` |-> `ty::tys`, `avs` |-> `av::avs`] abi_encoder_members_pre_address) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.INST [`actual` |-> `ready:venom_state`,
    `off` |-> `hl+LENGTH (FLAT (abi_tuple_tails pre pvs))`] abi_encoder_cursor_address) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.INST [`actual` |-> `ready:venom_state`] abi_encoder_members_child_buffer) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qpat_assum `abi_decoder_address_frame _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
  `abi_encoder_tuple_prefix hl pre pvs d ready.vs_memory` by
    (qpat_assum `ready.vs_memory = initial.vs_memory` (fn th => PURE_REWRITE_TAC [th]) >>
     first_assum ACCEPT_TAC) >>
  `abi_decoder_budget first last b cap ready` by
    (mp_tac (Q.INST [`s` |-> `initial:venom_state`, `t` |-> `ready:venom_state`]
      abi_decoder_budget_transport) >>
     impl_tac >- asm_simp_tac bool_ss [] >> asm_simp_tac bool_ss []) >>
  qpat_assum `hl = _` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]) >>
  qpat_assum `ho = _` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]) >>
  asm_simp_tac bool_ss [abi_encoder_members_inv_def, abi_decoder_address_frame_def] >> decide_tac
QED

Theorem abi_scratch_members_prepare_raw_transport:
  emit_op ADD [src;Lit (n2w so)] st = (elem_src,prepared) /\
  abi_scratch_members_inv ((ei,abi_sz,mem_sz,dyn)::infos) (ty::tys) (av::avs)
    pre pvs active dyn_ptr site slot first last lo st limit_st
    src dst sb so ho d hl output_size b cap initial /\
  prepared.cs_next_var <= limit_st.cs_next_var /\
  abi_encoder_member_phase_raw st prepared initial ready ==>
  abi_scratch_members_inv ((ei,abi_sz,mem_sz,dyn)::infos) (ty::tys) (av::avs)
    pre pvs active dyn_ptr site slot first last lo prepared limit_st
    src dst sb so ho d hl output_size b cap ready /\
  abi_scratch_input ei ty av prepared elem_src dst (sb+so) mem_sz d output_size first last b cap ready /\
  abi_decoder_address_frame st.cs_next_var initial ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_scratch_members_inv_layout >> strip_tac >>
  `LENGTH (enc ty av) <= output_size` by (Cases_on `dyn` >> fs[] >> decide_tac) >>
  qpat_assum `abi_scratch_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_members_inv_def]) >>
  `eval_operand src initial = SOME (n2w sb)` by fs[abi_scratch_members_pre_def] >>
  drule abi_encoder_emit_address_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >> drule abi_decoder_operand_live_emit >> strip_tac >>
  `st.cs_next_var <= prepared.cs_next_var /\ st.cs_next_id <= prepared.cs_next_id` by decide_tac >>
  `eval_operand (Lit (n2w so)) initial = SOME (n2w so)` by simp[eval_operand_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`] abi_encoder_member_binary_transport)) >> strip_tac >>
  `eval_operand elem_src ready = SOME (n2w (sb+so))` by fs[word_add_n2w] >>
  mp_tac (Q.INST [`actual` |-> `ready:venom_state`, `infos` |-> `(ei,abi_sz,mem_sz,dyn)::infos`,
    `tys` |-> `ty::tys`, `avs` |-> `av::avs`, `sz` |-> `output_size:num`]
    abi_scratch_members_pre_address) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  mp_tac (Q.INST [`actual` |-> `ready:venom_state`,
    `off` |-> `hl+LENGTH (FLAT (abi_tuple_tails pre pvs))`] abi_encoder_cursor_address) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  mp_tac (Q.INST [`st` |-> `prepared:compile_state`, `s` |-> `ready:venom_state`]
    abi_scratch_members_child_buffer) >> impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  mp_tac (Q.INST [`next` |-> `st.cs_next_var`, `s` |-> `initial:venom_state`,
    `t` |-> `ready:venom_state`] abi_scratch_address) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_encoder_tuple_prefix hl pre pvs d ready.vs_memory` by
    (qpat_assum `abi_decoder_address_frame _ _ _` (fn th =>
       assume_tac (CONJUNCT1 (CONJUNCT2 (PURE_REWRITE_RULE [abi_decoder_address_frame_def] th)))) >>
     gvs[Excl "enc_def"]) >>
  qpat_assum `hl = _` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]) >>
  qpat_assum `ho = _` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]) >>
  asm_simp_tac bool_ss [abi_scratch_members_inv_def] >> decide_tac
QED

Theorem abi_encoder_member_load_raw:
  emit_op MLOAD [src] st = (out,final) /\ eval_operand src initial = SOME p /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?ready. abi_encoder_member_phase_raw st final initial ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`opc` |-> `MLOAD`, `s` |-> `initial:venom_state`, `st'` |-> `final:compile_state`] abi_decoder_read_reentry) >>
  impl_tac >- asm_simp_tac (srw_ss()) [abi_decode_source_opcode_def] >> strip_tac >>
  qexists_tac `t with vs_inst_idx := LENGTH final.cs_current_insts` >>
  simp[abi_encoder_member_phase_raw_def] >> qexists_tac `t` >> simp[]
QED

Theorem abi_encoder_member_load_transport:
  emit_op MLOAD [src] st = (out,final) /\ eval_operand src initial = SOME p /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_encoder_member_phase_raw st final initial ready ==>
  eval_operand out ready = SOME (mload (w2n p) initial) /\
  fresh_vars_wrt limit_st ready /\ abi_decoder_address_frame st.cs_next_var initial ready /\
  ready.vs_current_bb = initial.vs_current_bb /\
  ready.vs_inst_idx = LENGTH final.cs_current_insts /\
  ready.vs_halted = initial.vs_halted
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`opc` |-> `MLOAD`, `s` |-> `initial:venom_state`, `st'` |-> `final:compile_state`] abi_decoder_read_reentry) >>
  impl_tac >- asm_simp_tac (srw_ss()) [abi_decode_source_opcode_def] >> strip_tac >>
  gvs[abi_encoder_member_phase_raw_def] >>
  gvs[abi_decoder_address_frame_def, fresh_vars_wrt_def, eval_op_inst_idx,
      abi_decode_load_def, update_var_def]
QED

Theorem abi_encoder_member_static_place_raw_transport:
  emit_op ADD [dst;Lit (n2w offset)] st = (head,prepared) /\
  abi_encoder_buffer_pre ei at av st src dst sb source_cap d output_size b cap initial /\
  offset+LENGTH (enc at av) <= output_size /\
  prepared.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_encoder_member_phase_raw st prepared initial ready ==>
  abi_encoder_pre ei at av prepared src head sb source_cap (d+offset) b cap ready /\
  fresh_vars_wrt limit_st ready /\ abi_decoder_address_frame st.cs_next_var initial ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `eval_operand dst initial = SOME (n2w d)` by fs[abi_encoder_buffer_pre_def] >>
  `eval_operand (Lit (n2w offset)) initial = SOME (n2w offset)` by simp[eval_operand_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`] abi_encoder_member_binary_transport)) >> strip_tac >>
  drule abi_decoder_operand_live_emit >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `st.cs_next_var <= prepared.cs_next_var` by decide_tac >>
  `eval_operand head ready = SOME (n2w (d+offset))` by fs[word_add_n2w] >>
  drule_all abi_encoder_child_pre_address >> simp[]
QED

Theorem abi_scratch_member_static_place_raw_transport:
  emit_op ADD [dst;Lit (n2w offset)] st = (head,prepared) /\
  abi_scratch_input ei at av st src dst sb source_cap d output_size first last b cap initial /\
  abi_decoder_budget first last b cap initial /\
  offset+LENGTH (enc at av) <= output_size /\
  prepared.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_encoder_member_phase_raw st prepared initial ready ==>
  abi_scratch_input ei at av prepared src head sb source_cap (d+offset)
    (LENGTH (enc at av)) first last b cap ready /\
  fresh_vars_wrt limit_st ready /\ abi_decoder_address_frame st.cs_next_var initial ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `eval_operand dst initial = SOME (n2w d)` by fs[abi_scratch_input_def] >>
  `eval_operand (Lit (n2w offset)) initial = SOME (n2w offset)` by simp[eval_operand_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`] abi_encoder_member_binary_transport)) >> strip_tac >>
  drule abi_decoder_operand_live_emit >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `st.cs_next_var <= prepared.cs_next_var` by decide_tac >>
  `eval_operand head ready = SOME (n2w (d+offset))` by fs[word_add_n2w] >>
  drule_all abi_scratch_address >>
  disch_then (qspecl_then [`abi_decoder_ids first last`, `[]`] strip_assume_tac) >>
  drule_all abi_scratch_child_input_address >> simp[]
QED

Theorem abi_encoder_member_cursor_raw:
  abi_encode_child_suffix head dyn_ptr offset child_len st = (out,final) /\
  eval_operand head initial = SOME (n2w h) /\ eval_operand dyn_ptr initial = SOME (n2w p) /\
  eval_operand offset initial = SOME (n2w off) /\ eval_operand child_len initial = SOME (n2w len) /\
  abi_decoder_operand_live st.cs_next_var dyn_ptr /\ abi_decoder_operand_live st.cs_next_var child_len /\
  h < dimword (:256) /\ p < dimword (:256) /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?ready. abi_encoder_member_phase_raw st final initial ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_child_suffix_sequence >> strip_tac >>
  qexists_tac `actual with vs_inst_idx := LENGTH final.cs_current_insts` >>
  simp[abi_encoder_member_phase_raw_def] >> qexists_tac `actual` >> simp[]
QED

Theorem abi_encoder_member_cursor_transport:
  abi_encode_child_suffix head dyn_ptr offset child_len st = (out,final) /\
  eval_operand head initial = SOME (n2w h) /\ eval_operand dyn_ptr initial = SOME (n2w p) /\
  eval_operand offset initial = SOME (n2w off) /\ eval_operand child_len initial = SOME (n2w len) /\
  abi_decoder_operand_live st.cs_next_var dyn_ptr /\ abi_decoder_operand_live st.cs_next_var child_len /\
  h < dimword (:256) /\ p < dimword (:256) /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_encoder_member_phase_raw st final initial ready ==>
  eval_operand out ready = SOME (n2w len) /\ fresh_vars_wrt limit_st ready /\
  ready.vs_memory = (mstore p (n2w (off+len)) (mstore h (n2w off) initial)).vs_memory /\
  abi_decode_footprint_frame [(h,32);(p,32)] initial ready /\
  ready.vs_allocas = initial.vs_allocas /\ ready.vs_alloca_next = initial.vs_alloca_next /\
  ready.vs_halted = initial.vs_halted /\
  (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
    eval_operand op ready = SOME w)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_child_suffix_sequence >> strip_tac >>
  gvs[abi_encoder_member_phase_raw_def] >>
  gvs[eval_op_inst_idx, fresh_vars_wrt_def, abi_decode_footprint_frame_def]
QED
