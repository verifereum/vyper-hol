(* Establish the full member-loop invariant by executing the real cursor initializer. *)
Theory abiEncoderComplexSetup
Ancestors
  abiEncoderComplexPrefix abiEncoderComplexLayout abiEncoderMembersBoundary
  abiEncoderMembersContract abiEncoderMembersDefs abiEncoderInput abiDecoderEffect
  abiDecoderAllocation abiDecoderReentry abiDecoderContract emitHelperProps compileEnv
  valueEncoding contractABI venomState words list arithmetic pred_set

Theorem abi_encoder_complex_prepare:
  abi_encode_complex_prefix infos st = (dyn_ptr,prepared) /\ fn_has_code st prepared func /\
  abi_encoder_members_pre infos tys avs st src dst sb 0 d output_size b cap initial /\
  LENGTH (enc (Tuple tys) (ListV avs)) <= output_size /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\
  prepared.cs_next_id <= last /\ prepared.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?ready slot.
    abi_encoder_members_inv infos tys avs [] [] T dyn_ptr st.cs_next_id slot first last
      st.cs_next_id prepared limit_st src dst sb 0 0 d (head_lengths tys 0) output_size b cap ready /\
    abi_decoder_effect first last st.cs_next_id prepared.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial ready /\ abi_decode_sim ctx func initial ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_members_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_members_pre_def]) >>
  drule abi_encoder_complex_input_metadata >> strip_tac >>
  drule abi_encoder_complex_prefix_shape >> strip_tac >>
  `st.cs_next_id IN abi_decoder_ids first last` by
    (simp_tac std_ss [abi_decoder_ids_def, GSPECIFICATION] >> decide_tac) >>
  drule_all abi_encoder_complex_prefix_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial ready` >>
  mp_tac (Q.INST [`site` |-> `st.cs_next_id`, `hi` |-> `prepared.cs_next_id`,
    `next` |-> `st.cs_next_var`, `outsz` |-> `output_size:num`, `actual` |-> `ready:venom_state`]
    abi_encoder_complex_prefix_effect) >>
  impl_tac >- (full_simp_tac bool_ss [] >> decide_tac) >> strip_tac >>
  mp_tac (Q.INST [`lo` |-> `st.cs_next_id`, `hi` |-> `prepared.cs_next_id`,
    `so` |-> `0:num`, `actual` |-> `ready:venom_state`] abi_encoder_members_pre_effect) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `st.cs_next_var <= prepared.cs_next_var` by decide_tac >>
  drule_all abi_encoder_members_pre_mono >> strip_tac >>
  qpat_assum `abi_encoder_complex_prefix_post _ _ _ _ _ _ _ _ _ _ ready`
    (qx_choose_then `slot` (MAP_EVERY assume_tac o CONJUNCTS) o
      PURE_REWRITE_RULE [abi_encoder_complex_prefix_post_def]) >>
  `abi_decoder_operand_live prepared.cs_next_var dyn_ptr` by
    (asm_simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
     rpt strip_tac >> decide_tac) >>
  `abi_encoder_cursor T dyn_ptr st.cs_next_id slot first st.cs_next_id prepared
    (head_lengths tys 0) ready` by
    (full_simp_tac bool_ss [abi_encoder_cursor_def] >> decide_tac) >>
  mp_tac (Q.INST [`active` |-> `T`, `site` |-> `st.cs_next_id`, `lo` |-> `st.cs_next_id`,
    `st` |-> `prepared`, `initial` |-> `ready:venom_state`, `hl` |-> `head_lengths tys 0`]
    abi_encoder_members_initial_inv) >>
  impl_tac >- (full_simp_tac bool_ss [] >> decide_tac) >> disch_tac >>
  qexistsl_tac [`ready`, `slot`] >> full_simp_tac bool_ss []
QED
