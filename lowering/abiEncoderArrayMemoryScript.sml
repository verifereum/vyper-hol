(* Persistent complete source data and the processed output prefix for encoder loops. *)
Theory abiEncoderArrayMemory
Ancestors
  abiEncoderArrayFrame abiEncoderArrayPrefix abiEncoderArrayLayout abiEncoderBufferFrame
  abiEncoderChildInputs abiEncoderInput abiDecoderEffect abiDecoderDynamicLoopSetup
  abiDecoderReentry abiDecoderFrame abiDecoderContract compileEnv valueEncoding contractABI
  venomState words arithmetic list

Theorem abi_encoder_buffer_pre_mono:
  abi_encoder_buffer_pre ei at av st src dst sb source_cap d output_size b cap s /\
  st.cs_next_var <= prepared.cs_next_var ==>
  abi_encoder_buffer_pre ei at av prepared src dst sb source_cap d output_size b cap s
Proof
  simp_tac bool_ss [abi_encoder_buffer_pre_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> asm_simp_tac bool_ss [] >>
  conj_tac >> irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]
QED

Theorem abi_encoder_buffer_pre_address:
  abi_encoder_buffer_pre ei at av st src dst sb source_cap d output_size b cap initial /\
  abi_decoder_address_frame st.cs_next_var initial actual /\ st.cs_next_var <= prepared.cs_next_var ==>
  abi_encoder_buffer_pre ei at av prepared src dst sb source_cap d output_size b cap actual
Proof
  simp_tac bool_ss [abi_encoder_buffer_pre_def, abi_decoder_address_frame_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `eval_operand src actual = SOME (n2w sb) /\ eval_operand dst actual = SOME (n2w d)` by
    (conj_tac >> first_x_assum irule >> asm_simp_tac bool_ss []) >>
  asm_simp_tac bool_ss [] >> conj_tac >> irule abi_decoder_operand_live_mono >>
  qexists_tac `st.cs_next_var` >> simp[]
QED

Definition abi_encoder_array_memory_def:
  abi_encoder_array_memory ei asz msz dyn ty avs st src dst sb source_cap d output_size b cap j s <=>
    abi_encoder_buffer_pre (AbiDynArray ei asz msz dyn) (Array NONE ty) (ListV avs)
      st src dst sb source_cap d output_size b cap s /\
    abi_encoder_array_prefix ty avs j d s.vs_memory /\
    LENGTH (enc (Array NONE ty) (ListV avs)) <= output_size
End

Theorem abi_encoder_array_memory_typed:
  abi_encoder_array_memory ei asz msz dyn ty avs st src dst sb source_cap d output_size b cap j s ==>
  has_type (Array NONE ty) (ListV avs) /\ j <= LENGTH avs /\ LENGTH avs < dimword (:256)
Proof
  simp_tac bool_ss [abi_encoder_array_memory_def, abi_encoder_buffer_pre_def,
    abi_encoder_array_prefix_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encoder_input_typed >> disch_tac >>
  drule_all abi_encoder_array_prefix_types >> asm_simp_tac bool_ss []
QED

Theorem abi_encoder_array_memory_address:
  abi_encoder_array_memory ei asz msz dyn ty avs st src dst sb source_cap d output_size b cap j initial /\
  abi_decoder_address_frame st.cs_next_var initial actual /\ st.cs_next_var <= prepared.cs_next_var ==>
  abi_encoder_array_memory ei asz msz dyn ty avs prepared src dst sb source_cap d output_size b cap j actual
Proof
  simp_tac bool_ss [abi_encoder_array_memory_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_buffer_pre_address >> disch_tac >>
  `actual.vs_memory = initial.vs_memory` by fs[abi_decoder_address_frame_def] >>
  asm_simp_tac bool_ss []
QED

Theorem abi_encoder_array_memory_advance:
  abi_encoder_array_memory ei asz msz dyn ty avs st src dst sb source_cap d output_size b cap j initial /\
  abi_decoder_effect first last lo hi st.cs_next_var limit_st d output_size b cap initial actual /\
  abi_encoder_array_prefix ty avs k d actual.vs_memory ==>
  abi_encoder_array_memory ei asz msz dyn ty avs st src dst sb source_cap d output_size b cap k actual
Proof
  simp_tac bool_ss [abi_encoder_array_memory_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_buffer_pre_effect >> asm_simp_tac bool_ss []
QED

Theorem abi_encoder_array_memory_scratch:
  abi_encoder_array_memory ei asz msz dyn ty avs st src dst sb source_cap d output_size b cap j initial /\
  abi_decoder_effect first last lo hi st.cs_next_var limit_st d output_size b cap initial actual /\
  abi_decode_footprint_frame fp initial actual /\ abi_footprint_disjoint d output_size fp ==>
  abi_encoder_array_memory ei asz msz dyn ty avs st src dst sb source_cap d output_size b cap j actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encoder_array_memory_typed >> strip_tac >>
  qpat_assum `abi_encoder_array_memory _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_array_memory_def]) >>
  drule_all abi_encoder_array_prefix_output_frame >> disch_tac >>
  drule_all abi_encoder_array_memory_advance >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_ARRAY_MEMORY_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder array memory invariant not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderArrayMemory");
