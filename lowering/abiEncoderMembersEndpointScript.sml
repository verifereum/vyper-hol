(* Pure member invariant advancement at the shared generator's endpoint.
   This late interpretation layer deliberately does not generate execution. *)
Theory abiEncoderMembersEndpoint
Ancestors
  abiEncoderMemberSourceAdapter abiEncoderMemberSourceInterpret
  abiEncoderMemberSourceContract abiEncoderMembersAdvance abiEncoderMembersLayout
  abiEncoderMembersContract abiEncoderMembersDefs abiEncoderTuple abiEncoderChildInputs
  abiEncoderMemberCode abiCanonicalWindows abiDecoderEffect abiDecoderContract
  compileEnv valueEncoding valueEncodingProps contractABI venomState words list arithmetic

Theorem abi_encoder_members_static_endpoint:
  compile_abi_encode_child dst elem_src ei F ho dyn_ptr st = (out,end_st) /\
  fn_has_code st end_st func /\
  (st.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_encoder_members_inv ((ei,abi_sz,mem_sz,F)::infos) (ty::tys) (av::avs)
    pre pvs active dyn_ptr site slot first last lo st limit_st
    src dst sb so ho d hl output_size b cap initial /\
  abi_encoder_buffer_pre ei ty av st elem_src dst (sb+so) mem_sz d output_size b cap initial /\
  end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var /\
  abi_encoder_spine_child_output
    (abi_encoder_member_core_post (ctx,func) (ty,av,sb+so,mem_sz,d+ho)
      (first,last,b,cap,limit_st))
    (ei,F,dst,elem_src,ho,dyn_ptr,st,end_st,out) initial actual ==>
  abi_encoder_members_inv infos tys avs (pre++[ty]) (pvs++[av]) active dyn_ptr site slot
    first last lo end_st limit_st src dst sb (so+mem_sz) (ho+abi_sz) d hl output_size b cap actual /\
  abi_decoder_effect first last lo end_st.cs_next_id st.cs_next_var
    limit_st d output_size b cap initial actual /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_members_inv_def]) >>
  mp_tac (SIMP_RULE bool_ss [] (Q.INST [`dyn` |-> `F`] abi_encoder_members_inv_layout)) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  drule abi_encoder_child_bounds >> strip_tac >>
  `ho+LENGTH (enc ty av) <= output_size` by decide_tac >>
  drule_all abi_encoder_member_source_static_output >> strip_tac >>
  qpat_assum `abi_encoder_buffer_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_buffer_pre_def]) >>
  drule_all abi_encoder_tuple_static_step >> strip_tac >>
  mp_tac (Q.INST [`off` |-> `hl+LENGTH (FLAT (abi_tuple_tails pre pvs))`,
    `sz` |-> `output_size:num`] abi_encoder_cursor_static) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac abi_encoder_members_prefix_advance >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `abi_encoder_cursor active dyn_ptr site slot first lo end_st
    (hl+LENGTH (FLAT (abi_tuple_tails (pre++[ty]) (pvs++[av])))) actual` by
    (qpat_assum `~is_dynamic ty` (fn dyn_th =>
       qpat_assum `LENGTH (FLAT (abi_tuple_tails (pre++[ty]) (pvs++[av]))) = _`
         (fn th => PURE_REWRITE_TAC [SIMP_RULE bool_ss [dyn_th, ADD_CLAUSES] th])) >>
     first_assum ACCEPT_TAC) >>
  `abi_decoder_effect first last lo end_st.cs_next_id st.cs_next_var
    limit_st d output_size b cap initial actual` by
    (irule abi_decoder_effect_widen >>
     qexistsl_tac [`d`, `end_st.cs_next_id`, `st.cs_next_id`, `st.cs_next_var`, `output_size`] >>
     asm_simp_tac bool_ss [] >> decide_tac) >>
  drule_all (Q.INST [`dyn` |-> `F`] abi_encoder_members_after_child) >> strip_tac >>
  asm_rewrite_tac []
QED

Theorem abi_encoder_members_dynamic_endpoint:
  compile_abi_encode_child dst elem_src ei T ho dyn_ptr st = (out,end_st) /\
  abi_encode_child_prefix dst ho dyn_ptr st = (ops,prepared) /\
  fn_has_code st end_st func /\
  (st.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_encoder_members_inv ((ei,abi_sz,mem_sz,T)::infos) (ty::tys) (av::avs)
    pre pvs active dyn_ptr site slot first last lo st limit_st
    src dst sb so ho d hl output_size b cap initial /\
  abi_encoder_buffer_pre ei ty av st elem_src dst (sb+so) mem_sz d output_size b cap initial /\
  end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var /\
  off = hl+LENGTH (FLAT (abi_tuple_tails pre pvs)) /\
  abi_encoder_spine_child_output
    (abi_encoder_member_dynamic_post (ctx,func) (ty,av,sb+so,mem_sz,d+off)
      (first,last,b,cap,limit_st) (FST ops,FST (SND ops),dyn_ptr,d+ho,off,slot,site))
    (ei,T,dst,elem_src,ho,dyn_ptr,st,end_st,out) initial actual ==>
  abi_encoder_members_inv infos tys avs (pre++[ty]) (pvs++[av]) active dyn_ptr site slot
    first last lo end_st limit_st src dst sb (so+mem_sz) (ho+abi_sz) d hl output_size b cap actual /\
  abi_decoder_effect first last lo end_st.cs_next_id st.cs_next_var
    limit_st d output_size b cap initial actual /\ abi_decode_sim ctx func initial actual
Proof
  reverse (Cases_on `active`) >- simp[abi_encoder_members_inv_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_members_inv_def]) >>
  mp_tac (SIMP_RULE bool_ss [] (Q.INST [`dyn` |-> `T`, `active` |-> `T`]
    abi_encoder_members_inv_layout)) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  drule abi_encoder_child_bounds >> strip_tac >>
  qpat_assum `abi_encoder_cursor _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE bool_ss [abi_encoder_cursor_def]) >>
  `ho+32 <= off /\ off+LENGTH (enc ty av) <= output_size /\
    mload slot initial = n2w off` by fs[] >>
  drule_all abi_encoder_member_source_dynamic_output >> strip_tac >>
  qpat_assum `abi_encoder_buffer_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_buffer_pre_def]) >>
  qpat_x_assum `abi_encoder_spine_child_output _ _ _ _` kall_tac >>
  qpat_x_assum `abi_encode_child_prefix _ _ _ _ = _` kall_tac >>
  mp_tac (Q.INST [`heads` |-> `ho:num`,
    `tails` |-> `LENGTH (FLAT (abi_tuple_tails pre pvs))`] abi_encoder_tuple_dynamic_step) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac abi_encoder_members_prefix_advance >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qpat_assum `mem_word_at slot actual.vs_memory = _`
    (assume_tac o PURE_REWRITE_RULE [mem_word_at_eq_mload]) >>
  mp_tac (Q.INST [`off` |-> `hl+LENGTH (FLAT (abi_tuple_tails pre pvs))`,
    `next_off` |-> `hl+LENGTH (FLAT (abi_tuple_tails (pre++[ty]) (pvs++[av])))`,
    `sz` |-> `output_size:num`, `owned_lo` |-> `lo:num`, `owned_hi` |-> `end_st.cs_next_id`]
    abi_encoder_cursor_finish) >>
  impl_tac >- asm_simp_tac bool_ss [ADD_ASSOC] >> strip_tac >>
  drule_all (Q.INST [`dyn` |-> `T`, `active` |-> `T`] abi_encoder_members_after_child) >>
  strip_tac >> asm_rewrite_tac []
QED

val _ = List.app (fn th =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms andalso null (Thm.hyp th)
    then () else raise Fail "source member endpoint has an admission, axiom or hypothesis"
  end) [abi_encoder_members_static_endpoint, abi_encoder_members_dynamic_endpoint];
