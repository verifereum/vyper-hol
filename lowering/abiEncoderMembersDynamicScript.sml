(* Execute a dynamic child and advance its parent cursor and remaining source invariant. *)
Theory abiEncoderMembersDynamic
Ancestors
  abiEncoderMembersAdvance abiEncoderMembersContract abiEncoderMembersDefs abiEncoderMembersLayout
  abiEncoderMemberStep abiEncoderMemberCode abiEncoderTuplePrefix abiEncoderCorrect abiEncoderChildInputs
  abiCanonicalWindows abiDecoderEffect abiDecoderContract abiDecoderLoop compileEnv
  valueEncoding contractABI venomState words list arithmetic

Theorem abi_encoder_members_dynamic_advance:
  abi_encoder_correct ei /\ compile_abi_encode_child dst elem_src ei T ho dyn_ptr st = (out,end_st) /\
  fn_has_code st end_st func /\
  (st.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_encoder_members_inv ((ei,abi_sz,mem_sz,T)::infos) (ty::tys) (av::avs)
    pre pvs active dyn_ptr site slot first last lo st limit_st
    src dst sb so ho d hl output_size b cap initial /\
  abi_encoder_buffer_pre ei ty av st elem_src dst (sb+so) mem_sz d output_size b cap initial /\
  end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var ==>
  ?actual. abi_encoder_members_inv infos tys avs (pre++[ty]) (pvs++[av]) active dyn_ptr site slot
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
  mp_tac (Q.INST [`heads` |-> `ho:num`, `tails` |-> `SUM (MAP2 abi_member_tail_size pre pvs)`,
    `off` |-> `hl+SUM (MAP2 abi_member_tail_size pre pvs)`,
    `src` |-> `elem_src`, `sb` |-> `sb+so`, `source_cap` |-> `mem_sz:num`]
    abi_encoder_dynamic_member_step) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  mp_tac abi_encoder_members_prefix_advance >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.INST [`off` |-> `hl+LENGTH (FLAT (abi_tuple_tails pre pvs))`,
    `next_off` |-> `hl+LENGTH (FLAT (abi_tuple_tails (pre++[ty]) (pvs++[av])))`,
    `sz` |-> `output_size:num`, `owned_lo` |-> `lo:num`, `owned_hi` |-> `end_st.cs_next_id`]
    abi_encoder_cursor_finish) >>
  impl_tac >- asm_simp_tac bool_ss [ADD_ASSOC] >> strip_tac >>
  mp_tac (Q.INST [`dyn` |-> `T`, `active` |-> `T`] abi_encoder_members_after_child) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_MEMBERS_DYNAMIC_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder dynamic members advance not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderMembersDynamic");
