(* Complete one actual member and restore the recursive suffix invariant.
   TOP-LEVEL: static/dynamic advance use the child's precise effect to protect
   the remaining source, processed prefix and registered parent cursor. *)
Theory abiScratchMembersAdvance
Ancestors
  abiScratchMembers abiScratchMemberStep abiScratchCursor abiScratchEncoderContract
  abiScratchEffect abiEncoderMembersDefs abiEncoderMembersLayout abiEncoderMemberCode
  abiEncoderTuple abiCanonicalWindows abiDecoderDynamicLoopSetup abiDecoderFootprint
  abiDecoderReentry abiDecoderContract abiDecoderLoop compileEnv valueEncoding contractABI
  venomState words list arithmetic

Theorem abi_scratch_cursor_mono:
  abi_encoder_cursor active dyn_ptr site slot first lo st off s /\
  st.cs_next_var <= end_st.cs_next_var /\ st.cs_next_id <= end_st.cs_next_id ==>
  abi_encoder_cursor active dyn_ptr site slot first lo end_st off s
Proof
  Cases_on `active` >> simp_tac bool_ss [abi_encoder_cursor_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_operand_live end_st.cs_next_var dyn_ptr` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  asm_simp_tac bool_ss [] >> decide_tac
QED

Theorem abi_scratch_members_static_advance:
  abi_scratch_encoder ei /\ compile_abi_encode_child dst elem_src ei F ho dyn_ptr st = (out,end_st) /\
  fn_has_code st end_st func /\
  (st.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_scratch_members_inv ((ei,abi_sz,mem_sz,F)::infos) (ty::tys) (av::avs)
    pre pvs active dyn_ptr site slot first last lo st limit_st
    src dst sb so ho d hl output_size b cap initial /\
  abi_scratch_input ei ty av st elem_src dst (sb+so) mem_sz d output_size first last b cap initial /\
  end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var ==>
  ?actual. abi_scratch_members_inv infos tys avs (pre++[ty]) (pvs++[av]) active dyn_ptr site slot
      first last lo end_st limit_st src dst sb (so+mem_sz) (ho+abi_sz) d hl output_size b cap actual /\
    abi_scratch_effect first last lo end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial actual /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_scratch_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_members_inv_def]) >>
  mp_tac (SIMP_RULE bool_ss [] (Q.INST [`dyn` |-> `F`] abi_scratch_members_inv_layout)) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  drule abi_encoder_child_bounds >> strip_tac >>
  mp_tac (Q.INST [`heads` |-> `ho:num`, `tails` |-> `SUM (MAP2 abi_member_tail_size pre pvs)`,
    `src` |-> `elem_src`, `sb` |-> `sb+so`, `source_cap` |-> `mem_sz:num`] abi_scratch_static_member_step) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  `abi_encoder_cursor active dyn_ptr site slot first lo st
    (hl+LENGTH (FLAT (abi_tuple_tails pre pvs))) actual` by
    (reverse (Cases_on `active`) >- simp[abi_encoder_cursor_def] >>
     mp_tac (Q.INST [`active` |-> `T`, `cursor_op` |-> `dyn_ptr:operand`, `owned_lo` |-> `st.cs_next_id`,
       `owned_hi` |-> `end_st.cs_next_id`, `next` |-> `st.cs_next_var`,
       `off` |-> `hl+LENGTH (FLAT (abi_tuple_tails pre pvs))`, `sz` |-> `output_size:num`]
       abi_scratch_cursor_protected) >>
     impl_tac >- (fs[abi_encoder_cursor_def, abi_scratch_input_def] >> decide_tac) >> simp[]) >>
  drule_all (Q.INST [`s` |-> `actual:venom_state`, `end_st` |-> `end_st:compile_state`]
    abi_scratch_cursor_mono) >> disch_tac >>
  mp_tac abi_encoder_members_prefix_advance >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `abi_encoder_cursor active dyn_ptr site slot first lo end_st
    (hl+LENGTH (FLAT (abi_tuple_tails (pre++[ty]) (pvs++[av])))) actual` by
    (qpat_assum `~is_dynamic ty` (fn dyn_th =>
       qpat_assum `LENGTH (FLAT (abi_tuple_tails (pre++[ty]) (pvs++[av]))) = _`
         (fn th => PURE_REWRITE_TAC [SIMP_RULE bool_ss [dyn_th, ADD_CLAUSES] th])) >>
     first_assum ACCEPT_TAC) >>
  `abi_scratch_effect first last lo end_st.cs_next_id st.cs_next_var
    limit_st d output_size b cap initial actual` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`, `end_st.cs_next_id`, `st.cs_next_id`, `st.cs_next_var`, `output_size`] >>
     asm_simp_tac bool_ss [LESS_EQ_REFL] >> decide_tac) >>
  mp_tac (Q.INST [`dyn` |-> `F`] abi_scratch_members_after_child) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

Theorem abi_scratch_members_dynamic_advance:
  abi_scratch_encoder ei /\ compile_abi_encode_child dst elem_src ei T ho dyn_ptr st = (out,end_st) /\
  fn_has_code st end_st func /\
  abi_scratch_members_inv ((ei,abi_sz,mem_sz,T)::infos) (ty::tys) (av::avs)
    pre pvs active dyn_ptr site slot first last lo st limit_st
    src dst sb so ho d hl output_size b cap initial /\
  abi_scratch_input ei ty av st elem_src dst (sb+so) mem_sz d output_size first last b cap initial /\
  end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var ==>
  ?actual. abi_scratch_members_inv infos tys avs (pre++[ty]) (pvs++[av]) active dyn_ptr site slot
      first last lo end_st limit_st src dst sb (so+mem_sz) (ho+abi_sz) d hl output_size b cap actual /\
    abi_scratch_effect first last lo end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial actual /\ abi_decode_sim ctx func initial actual
Proof
  reverse (Cases_on `active`) >- simp[abi_scratch_members_inv_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_scratch_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_members_inv_def]) >>
  mp_tac (SIMP_RULE bool_ss [] (Q.INST [`dyn` |-> `T`, `active` |-> `T`]
    abi_scratch_members_inv_layout)) >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  drule abi_encoder_child_bounds >> strip_tac >>
  qpat_assum `abi_encoder_cursor _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE bool_ss [abi_encoder_cursor_def]) >>
  mp_tac (Q.INST [`heads` |-> `ho:num`, `tails` |-> `SUM (MAP2 abi_member_tail_size pre pvs)`,
    `off` |-> `hl+SUM (MAP2 abi_member_tail_size pre pvs)`, `src` |-> `elem_src`,
    `sb` |-> `sb+so`, `source_cap` |-> `mem_sz:num`] abi_scratch_dynamic_member_step) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  mp_tac abi_encoder_members_prefix_advance >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.INST [`active` |-> `T`, `cursor_op` |-> `dyn_ptr:operand`,
    `off` |-> `hl+LENGTH (FLAT (abi_tuple_tails pre pvs))`,
    `next_off` |-> `hl+LENGTH (FLAT (abi_tuple_tails (pre++[ty]) (pvs++[av])))`,
    `sz` |-> `output_size:num`, `owned_lo` |-> `lo:num`, `owned_hi` |-> `end_st.cs_next_id`,
    `next` |-> `st.cs_next_var`] abi_scratch_cursor_registered) >>
  impl_tac >- asm_simp_tac bool_ss [ADD_ASSOC, LESS_EQ_REFL] >> disch_tac >>
  drule_all (Q.INST [`s` |-> `actual:venom_state`, `end_st` |-> `end_st:compile_state`]
    abi_scratch_cursor_mono) >> disch_tac >>
  mp_tac (Q.INST [`dyn` |-> `T`, `active` |-> `T`] abi_scratch_members_after_child) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

Theorem abi_scratch_members_child_advance:
  abi_scratch_encoder ei /\ compile_abi_encode_child dst elem_src ei dyn ho dyn_ptr st = (out,end_st) /\
  fn_has_code st end_st func /\
  (st.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_scratch_members_inv ((ei,abi_sz,mem_sz,dyn)::infos) (ty::tys) (av::avs)
    pre pvs active dyn_ptr site slot first last lo st limit_st
    src dst sb so ho d hl output_size b cap initial /\
  abi_scratch_input ei ty av st elem_src dst (sb+so) mem_sz d output_size first last b cap initial /\
  end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var ==>
  ?actual. abi_scratch_members_inv infos tys avs (pre++[ty]) (pvs++[av]) active dyn_ptr site slot
      first last lo end_st limit_st src dst sb (so+mem_sz) (ho+abi_sz) d hl output_size b cap actual /\
    abi_scratch_effect first last lo end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial actual /\ abi_decode_sim ctx func initial actual
Proof
  Cases_on `dyn`
  >- (disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
      drule_all abi_scratch_members_dynamic_advance >> disch_then (qspec_then `ctx` ACCEPT_TAC)) >>
  ACCEPT_TAC abi_scratch_members_static_advance
QED
