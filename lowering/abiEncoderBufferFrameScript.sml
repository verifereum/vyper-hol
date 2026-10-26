(* Child/sibling writes preserve the complete source represented by a parent buffer precondition. *)
Theory abiEncoderBufferFrame
Ancestors
  abiEncoderChildInputs abiEncoderInputFrame abiEncoderInputLayout abiEncoderInput abiDecoderEffect
  abiDecoderDynamicLoopSetup abiDecoderReentry abiDecoderFrame abiDecoderContract
  compileEnv valueEncoding venomState words list arithmetic

Theorem abi_encoder_buffer_pre_effect:
  abi_encoder_buffer_pre ei at av st src dst sb source_cap d output_size b cap initial /\
  abi_decoder_effect first last lo hi st.cs_next_var limit_st d output_size b cap initial actual ==>
  abi_encoder_buffer_pre ei at av st src dst sb source_cap d output_size b cap actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_buffer_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_buffer_pre_def]) >>
  qpat_assum `abi_decoder_effect _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_effect_def]) >>
  `abi_footprint_disjoint sb source_cap [(d,output_size);(b,cap)]` by
    asm_simp_tac (srw_ss()) [abi_footprint_disjoint_def, DISJ_IMP_THM, FORALL_AND_THM] >>
  drule_all abi_encoder_input_frame >> strip_tac >>
  `eval_operand src actual = SOME (n2w sb) /\ eval_operand dst actual = SOME (n2w d)` by
    (conj_tac >> first_x_assum irule >> asm_simp_tac bool_ss []) >>
  asm_simp_tac bool_ss [abi_encoder_buffer_pre_def]
QED

Theorem abi_encoder_tuple_type_unique:
  abi_encoder_tuple_type at ats /\ abi_encoder_tuple_type at bts ==> ats = bts
Proof
  rw[abi_encoder_tuple_type_def] >> gvs[]
QED

Theorem abi_encoder_complex_selected_input:
  abi_encoder_input (AbiComplex infos) at (ListV avs) sb source_cap mem /\
  abi_encoder_tuple_type at ats /\ i < LENGTH infos /\ EL i infos = (ei,abi_sz,mem_sz,dyn) ==>
  abi_encoder_input ei (EL i ats) (EL i avs)
    (sb+abi_encoder_member_span (TAKE i infos)) mem_sz mem /\
  abi_sz = abi_member_head_size (EL i ats) /\ dyn = is_dynamic (EL i ats) /\
  abi_encoder_member_span (TAKE i infos)+mem_sz <= source_cap
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `abi_encoder_input _ _ _ _ _ _`
    (qx_choose_then `layout` (qx_choose_then `values` strip_assume_tac) o
      REWRITE_RULE [abi_encoder_complex_input_iff]) >>
  `layout = ats` by
    (irule abi_encoder_tuple_type_unique >> qexists_tac `at` >> asm_simp_tac bool_ss []) >>
  gvs[] >> qpat_x_assum `!i ei abi_sz mem_sz dyn. _`
    (qspecl_then [`i`, `ei`, `abi_sz`, `mem_sz`, `dyn`] mp_tac) >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac abi_encoder_member_slot_bound >> impl_tac >- asm_simp_tac (srw_ss()) [] >> strip_tac >>
  asm_simp_tac bool_ss [] >> decide_tac
QED

Theorem abi_encoder_member_buffer_pre:
  abi_encoder_buffer_pre (AbiComplex infos) at (ListV avs)
    st src dst sb source_cap d output_size b cap initial /\
  abi_encoder_tuple_type at ats /\ i < LENGTH infos /\ EL i infos = (ei,abi_sz,mem_sz,dyn) /\
  abi_decoder_address_frame st.cs_next_var initial actual /\ st.cs_next_var <= child_st.cs_next_var /\
  abi_decoder_operand_live child_st.cs_next_var child_src /\
  eval_operand child_src actual = SOME (n2w (sb+abi_encoder_member_span (TAKE i infos))) ==>
  abi_encoder_buffer_pre ei (EL i ats) (EL i avs) child_st child_src dst
    (sb+abi_encoder_member_span (TAKE i infos)) mem_sz d output_size b cap actual /\
  abi_sz = abi_member_head_size (EL i ats) /\ dyn = is_dynamic (EL i ats)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_buffer_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_buffer_pre_def]) >>
  drule_all abi_encoder_complex_selected_input >> strip_tac >>
  `actual.vs_memory = initial.vs_memory /\ eval_operand dst actual = SOME (n2w d)`
    by fs[abi_decoder_address_frame_def] >>
  `abi_decoder_operand_live child_st.cs_next_var dst` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  asm_simp_tac bool_ss [abi_encoder_buffer_pre_def] >> decide_tac
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_BUFFER_FRAME_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder buffer frame not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderBufferFrame");
