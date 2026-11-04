(* Incoming state for a remaining member list and its optional parent cursor. *)
Theory abiEncoderMembersDefs
Ancestors
  abiEncoderMembersInput abiEncoderInputFrame abiEncoderInput abiEncoderDynamic abiDecoderEffect
  abiDecoderDynamicLoopSetup abiDecoderAllocation abiDecoderReentry abiDecoderFrame
  abiDecoderContract compileEnv valueEncoding venomState finite_map words list arithmetic

Definition abi_encoder_members_pre_def:
  abi_encoder_members_pre infos tys avs st src dst sb so d output_size b cap s <=>
    abi_encoder_input (AbiComplex infos) (Tuple tys) (ListV avs)
      (sb+so) (abi_encoder_member_span infos) s.vs_memory /\
    eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
    abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
    sb+so+abi_encoder_member_span infos < dimword (:256) /\
    d+output_size < dimword (:256) /\
    (sb+so+abi_encoder_member_span infos <= d \/ d+output_size <= sb+so) /\
    (sb+so+abi_encoder_member_span infos <= b \/ b+cap <= sb+so) /\
    (d+output_size <= b \/ b+cap <= d)
End

Definition abi_encoder_cursor_def:
  abi_encoder_cursor active dyn_ptr site slot first lo st off s <=>
    active ==>
      abi_decoder_operand_live st.cs_next_var dyn_ptr /\
      eval_operand dyn_ptr s = SOME (n2w slot) /\ mload slot s = n2w off /\
      first <= site /\ site < st.cs_next_id /\ lo <= site /\
      FLOOKUP s.vs_allocas site = SOME (slot,32)
End

Theorem abi_encoder_members_pre_mono:
  abi_encoder_members_pre infos tys avs st src dst sb so d output_size b cap s /\
  st.cs_next_var <= prepared.cs_next_var ==>
  abi_encoder_members_pre infos tys avs prepared src dst sb so d output_size b cap s
Proof
  simp_tac bool_ss [abi_encoder_members_pre_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> asm_simp_tac bool_ss [] >>
  conj_tac >> irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]
QED

Theorem abi_encoder_members_pre_address:
  abi_encoder_members_pre infos tys avs st src dst sb so d output_size b cap initial /\
  abi_decoder_address_frame st.cs_next_var initial actual /\ st.cs_next_var <= prepared.cs_next_var ==>
  abi_encoder_members_pre infos tys avs prepared src dst sb so d output_size b cap actual
Proof
  simp_tac bool_ss [abi_encoder_members_pre_def, abi_decoder_address_frame_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `eval_operand src actual = SOME (n2w sb) /\ eval_operand dst actual = SOME (n2w d)` by
    (conj_tac >> first_x_assum irule >> asm_simp_tac bool_ss []) >>
  asm_simp_tac bool_ss [] >> conj_tac >> irule abi_decoder_operand_live_mono >>
  qexists_tac `st.cs_next_var` >> simp[]
QED

Theorem abi_encoder_members_pre_effect:
  abi_encoder_members_pre infos tys avs st src dst sb so d output_size b cap initial /\
  abi_decoder_effect first last lo hi st.cs_next_var limit_st d output_size b cap initial actual ==>
  abi_encoder_members_pre infos tys avs st src dst sb so d output_size b cap actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_members_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_members_pre_def]) >>
  qpat_assum `abi_decoder_effect _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_effect_def]) >>
  `abi_footprint_disjoint (sb+so) (abi_encoder_member_span infos) [(d,output_size);(b,cap)]` by
    asm_simp_tac (srw_ss()) [abi_footprint_disjoint_def, DISJ_IMP_THM, FORALL_AND_THM] >>
  drule_all abi_encoder_input_frame >> strip_tac >>
  `eval_operand src actual = SOME (n2w sb) /\ eval_operand dst actual = SOME (n2w d)` by
    (conj_tac >> first_x_assum irule >> asm_simp_tac bool_ss []) >>
  asm_simp_tac bool_ss [abi_encoder_members_pre_def]
QED

Theorem abi_encoder_cursor_address:
  abi_encoder_cursor active dyn_ptr site slot first lo st off initial /\
  abi_decoder_address_frame st.cs_next_var initial actual /\
  st.cs_next_var <= prepared.cs_next_var /\ st.cs_next_id <= prepared.cs_next_id ==>
  abi_encoder_cursor active dyn_ptr site slot first lo prepared off actual
Proof
  Cases_on `active` >> simp_tac bool_ss [abi_encoder_cursor_def, abi_decoder_address_frame_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `eval_operand dyn_ptr actual = SOME (n2w slot)` by (first_x_assum irule >> simp[]) >>
  `abi_decoder_operand_live prepared.cs_next_var dyn_ptr` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  `mload slot actual = n2w off` by fs[mload_def] >>
  asm_simp_tac bool_ss [] >> decide_tac
QED

Theorem abi_encoder_cursor_finish:
  abi_encoder_cursor T dyn_ptr site slot first lo st off initial /\
  abi_decoder_effect first last owned_lo owned_hi st.cs_next_var limit_st d sz b cap initial actual /\
  st.cs_next_var <= end_st.cs_next_var /\ st.cs_next_id <= end_st.cs_next_id /\
  FLOOKUP actual.vs_allocas site = SOME (slot,32) /\ mload slot actual = n2w next_off ==>
  abi_encoder_cursor T dyn_ptr site slot first lo end_st next_off actual
Proof
  simp_tac bool_ss [abi_encoder_cursor_def] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `eval_operand dyn_ptr actual = SOME (n2w slot)` by
    (imp_res_tac abi_encoder_effect_operand >> simp[]) >>
  `abi_decoder_operand_live end_st.cs_next_var dyn_ptr` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  asm_simp_tac bool_ss [] >> decide_tac
QED

Theorem abi_encoder_cursor_static:
  abi_encoder_cursor active dyn_ptr site slot first lo st off initial /\
  abi_decoder_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
    limit_st d sz b cap initial actual /\
  st.cs_next_var <= end_st.cs_next_var /\ st.cs_next_id <= end_st.cs_next_id /\
  end_st.cs_next_id <= last ==>
  abi_encoder_cursor active dyn_ptr site slot first lo end_st off actual
Proof
  Cases_on `active` >> simp_tac bool_ss [abi_encoder_cursor_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> `site < last` by decide_tac >>
  mp_tac (Q.INST [`lo` |-> `st.cs_next_id`, `hi` |-> `end_st.cs_next_id`,
    `next` |-> `st.cs_next_var`, `s` |-> `initial:venom_state`, `t` |-> `actual:venom_state`]
    abi_decoder_effect_protected_slot) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `eval_operand dyn_ptr actual = SOME (n2w slot)` by
    (imp_res_tac abi_encoder_effect_operand >> simp[]) >>
  `abi_decoder_operand_live end_st.cs_next_var dyn_ptr` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  asm_simp_tac bool_ss [] >> decide_tac
QED
