(* Concrete endpoints, independent of the invariant transported by a member. *)
Theory abiEncoderMemberPhaseExec
Ancestors
  abiEncoderMemberPhaseRaw
  abiScratchMembers abiScratchAddress abiScratchChild abiScratchEncoderContract
  abiEncoderChildSuffix abiDecoderFrame abiEncoderMembersBoundary
  abiDecoderAllocation abiDecoderIndexInit abiDecoderProtectedScratch pred_set
  abiEncoderArrayTail abiBuiltinPrefix abiEncoderExtendSim
  abiEncoderMembersContract abiEncoderMembersDefs abiEncoderMembersSource
  abiEncoderTuple abiEncoderChildInputs abiEncoderInput abiCanonicalWindows
  abiDecoderArrayInitExec abiDecoderLoop emitHelperProps valueEncoding arithmetic
  abiEncoderAddressReach abiDecoderReentryAddress abiDecoderDynamicLoopSetup
  abiDecoderReentry abiDecoderContract fragExec compileEnv venomState
  venomExecSemantics venomInst emitHelper instIdxIndep words list


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


Theorem abi_encoder_complex_finish_raw_transport:
  abi_encoder_members_inv [] [] [] tys avs T dyn_ptr site slot first last lo st limit_st
    src dst sb so ho d hl output_size b cap encoded /\
  emit_op MLOAD [dyn_ptr] st = (out,end_st) /\
  end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var /\ 
  abi_encoder_member_phase_raw st end_st encoded actual ==>
  mem_bytes_at d (LENGTH (enc (Tuple tys) (ListV avs))) actual.vs_memory =
    enc (Tuple tys) (ListV avs) /\
  eval_operand out actual = SOME (n2w (LENGTH (enc (Tuple tys) (ListV avs)))) /\
  fresh_vars_wrt limit_st actual /\ abi_decoder_address_frame st.cs_next_var encoded actual /\
  actual.vs_current_bb = end_st.cs_current_bb /\ actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\
  ~actual.vs_halted
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule abi_encoder_members_final_output >> strip_tac >>
  qpat_assum `abi_encoder_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ encoded`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_members_inv_def]) >>
  qpat_x_assum `abi_encoder_cursor T _ _ _ _ _ _ (LENGTH _) _`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE bool_ss [abi_encoder_cursor_def]) >>
  `site IN abi_decoder_ids first last` by
    (simp_tac std_ss [abi_decoder_ids_def, GSPECIFICATION] >> decide_tac) >>
  drule_all abi_decoder_budget_site_bounds >> strip_tac >>
  drule abi_decoder_budget_word_bound >> strip_tac >> `slot < dimword (:256)` by decide_tac >>
  drule_all abi_encoder_member_load_transport >> strip_tac >>
  drule abi_encoder_emit_address_shape >> strip_tac >>
  gvs[abi_decoder_address_frame_def, w2n_n2w]
QED

Theorem abi_scratch_complex_finish_raw_transport:
  abi_scratch_members_inv [] [] [] tys avs T dyn_ptr site slot first last lo st limit_st
    src dst sb so ho d hl output_size b cap encoded /\
  emit_op MLOAD [dyn_ptr] st = (out,end_st) /\
  end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var /\
  abi_encoder_member_phase_raw st end_st encoded actual ==>
  mem_bytes_at d (LENGTH (enc (Tuple tys) (ListV avs))) actual.vs_memory =
    enc (Tuple tys) (ListV avs) /\
  eval_operand out actual = SOME (n2w (LENGTH (enc (Tuple tys) (ListV avs)))) /\
  fresh_vars_wrt limit_st actual /\ abi_decoder_address_frame st.cs_next_var encoded actual /\
  actual.vs_current_bb = end_st.cs_current_bb /\ actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\
  ~actual.vs_halted
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule abi_scratch_members_final_output >> strip_tac >>
  qpat_assum `abi_scratch_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ encoded`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_members_inv_def]) >>
  qpat_x_assum `abi_encoder_cursor T _ _ _ _ _ _ (LENGTH _) _`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE bool_ss [abi_encoder_cursor_def]) >>
  `site IN abi_decoder_ids first last` by
    (simp_tac std_ss [abi_decoder_ids_def, GSPECIFICATION] >> decide_tac) >>
  drule_all abi_decoder_budget_site_bounds >> strip_tac >>
  drule abi_decoder_budget_word_bound >> strip_tac >> `slot < dimword (:256)` by decide_tac >>
  drule_all abi_encoder_member_load_transport >> strip_tac >>
  drule abi_encoder_emit_address_shape >> strip_tac >>
  gvs[abi_decoder_address_frame_def, w2n_n2w]
QED


Theorem abi_encoder_members_prepare_raw_compat:
  emit_op ADD [src;Lit (n2w so)] st = (elem_src,prepared) /\ fn_has_code st prepared func /\
  abi_encoder_members_inv ((ei,abi_sz,mem_sz,dyn)::infos) (ty::tys) (av::avs)
    pre pvs active dyn_ptr site slot first last lo st limit_st
    src dst sb so ho d hl output_size b cap initial /\
  prepared.cs_next_var <= limit_st.cs_next_var ==>
  ?ready. abi_encoder_members_inv ((ei,abi_sz,mem_sz,dyn)::infos) (ty::tys) (av::avs)
      pre pvs active dyn_ptr site slot first last lo prepared limit_st
      src dst sb so ho d hl output_size b cap ready /\
    abi_encoder_buffer_pre ei ty av prepared elem_src dst (sb+so) mem_sz d output_size b cap ready /\
    abi_decoder_address_frame st.cs_next_var initial ready /\ abi_decode_sim ctx func initial ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
   initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts /\
   eval_operand src initial = SOME (n2w sb)` by
    fs[abi_encoder_members_inv_def, abi_encoder_members_pre_def] >>
  `eval_operand (Lit (n2w so)) initial = SOME (n2w so)` by simp[eval_operand_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`] abi_encoder_member_binary_raw)) >> strip_tac >>
  drule_all abi_encoder_members_prepare_raw_transport >> strip_tac >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`] abi_encoder_member_binary_raw_sim)) >>
  disch_then (qspec_then `ctx` assume_tac) >>
  qexists_tac `ready` >> simp[]
QED

Theorem abi_scratch_members_prepare_raw_compat:
  emit_op ADD [src;Lit (n2w so)] st = (elem_src,prepared) /\ fn_has_code st prepared func /\
  abi_scratch_members_inv ((ei,abi_sz,mem_sz,dyn)::infos) (ty::tys) (av::avs)
    pre pvs active dyn_ptr site slot first last lo st limit_st
    src dst sb so ho d hl output_size b cap initial /\
  prepared.cs_next_var <= limit_st.cs_next_var ==>
  ?ready. abi_scratch_members_inv ((ei,abi_sz,mem_sz,dyn)::infos) (ty::tys) (av::avs)
      pre pvs active dyn_ptr site slot first last lo prepared limit_st
      src dst sb so ho d hl output_size b cap ready /\
    abi_scratch_input ei ty av prepared elem_src dst (sb+so) mem_sz d output_size first last b cap ready /\
    abi_decoder_address_frame st.cs_next_var initial ready /\ abi_decode_sim ctx func initial ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
   initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts /\
   eval_operand src initial = SOME (n2w sb)` by
    fs[abi_scratch_members_inv_def, abi_scratch_members_pre_def] >>
  `eval_operand (Lit (n2w so)) initial = SOME (n2w so)` by simp[eval_operand_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`] abi_encoder_member_binary_raw)) >> strip_tac >>
  drule_all abi_scratch_members_prepare_raw_transport >> strip_tac >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`] abi_encoder_member_binary_raw_sim)) >>
  disch_then (qspec_then `ctx` assume_tac) >>
  qexists_tac `ready` >> simp[]
QED
