(* Transfer successful child observations to the next member's pure invariant. *)
Theory abiEncoderMembersAdvance
Ancestors
  abiEncoderMembersContract abiEncoderMembersDefs abiEncoderMembersSource
  abiEncoderMembersLayout abiEncoderTuple abiEncoderInput abiDecodeRanges abiCanonicalWindows
  abiDecoderEffect abiDecoderReentry abiDecoderContract compileEnv valueEncoding contractABI
  venomState words list arithmetic

Theorem abi_encoder_members_after_child:
  abi_encoder_members_inv ((ei,abi_sz,mem_sz,dyn)::infos) (ty::tys) (av::avs)
    pre pvs active dyn_ptr site slot first last lo st limit_st
    src dst sb so ho d hl output_size b cap initial /\
  abi_decoder_effect first last lo end_st.cs_next_id st.cs_next_var
    limit_st d output_size b cap initial actual /\
  abi_encoder_tuple_prefix hl (pre++[ty]) (pvs++[av]) d actual.vs_memory /\
  abi_encoder_cursor active dyn_ptr site slot first lo end_st
    (hl+LENGTH (FLAT (abi_tuple_tails (pre++[ty]) (pvs++[av])))) actual /\
  st.cs_next_var <= end_st.cs_next_var /\ st.cs_next_id <= end_st.cs_next_id /\
  end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var /\
  ~actual.vs_halted /\ actual.vs_current_bb = end_st.cs_current_bb /\
  actual.vs_inst_idx = LENGTH end_st.cs_current_insts ==>
  abi_encoder_members_inv infos tys avs (pre++[ty]) (pvs++[av]) active dyn_ptr site slot first last lo
    end_st limit_st src dst sb (so+mem_sz) (ho+abi_sz) d hl output_size b cap actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_members_inv_def]) >>
  mp_tac (Q.INST [`infos` |-> `(ei,abi_sz,mem_sz,dyn)::infos`, `tys` |-> `ty::tys`,
    `avs` |-> `av::avs`, `hi` |-> `end_st.cs_next_id`] abi_encoder_members_pre_effect) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.INST [`infos` |-> `(ei,abi_sz,mem_sz,dyn)::infos`, `tys` |-> `ty::tys`,
    `avs` |-> `av::avs`, `prepared` |-> `end_st`, `s` |-> `actual:venom_state`]
    abi_encoder_members_pre_mono) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.INST [`st` |-> `end_st`, `s` |-> `actual:venom_state`] abi_encoder_members_pre_cons) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac abi_encoder_members_prefix_advance >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qpat_assum `abi_decoder_effect _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_effect_def]) >>
  `first <= end_st.cs_next_id /\ lo <= end_st.cs_next_id` by decide_tac >>
  PURE_REWRITE_TAC [abi_encoder_members_inv_def, GSYM APPEND_ASSOC, APPEND] >>
  asm_simp_tac bool_ss [] >>
  qpat_x_assum `active \/ EVERY _ _` mp_tac >> simp_tac (srw_ss()) [] >>
  rpt strip_tac >> asm_simp_tac bool_ss []
QED
