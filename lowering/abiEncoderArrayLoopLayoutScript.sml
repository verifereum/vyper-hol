(* Read the real generated header/backedge blocks and their PHI-free entry points. *)
Theory abiEncoderArrayLoopLayout
Ancestors
  abiEncoderArrayHeader abiEncoderArrayBodyCode abiEncoderArrayDynamicCode abiEncoderArrayCode
  abiEncoderArrayAddress abiDecoderDynamicLoopSetup abiDecoderLoopEmit abiDecoderExecution abiDecoderLoopCode
  abiEncoderAdmissible abiDecoderContract fragExec compileEnv emitHelperProps emitHelper
  venomInst venomExecSemantics words list rich_list arithmetic

Theorem abi_encode_array_header_code:
  abi_encode_array_header ip count_op owner_st = (labels,body_st) /\
  fn_has_code owner_st body_st func ==>
  body_st.cs_next_var = owner_st.cs_next_var+3 /\ body_st.cs_next_id = owner_st.cs_next_id+5 /\
  body_st.cs_current_bb = FST (SND labels) /\ body_st.cs_current_insts = [] /\
  lookup_block (FST labels) func.fn_blocks = SOME <|bb_label := FST labels; bb_instructions :=
    abi_encode_array_header_insts (owner_st.cs_next_id+1) ip count_op
      (STRING #"%" (toString owner_st.cs_next_var))
      (STRING #"%" (toString (owner_st.cs_next_var+1)))
      (STRING #"%" (toString (owner_st.cs_next_var+2)))
      (FST (SND labels)) (SND (SND labels))|> /\
  lookup_block owner_st.cs_current_bb func.fn_blocks = SOME
    <|bb_label := owner_st.cs_current_bb; bb_instructions := owner_st.cs_current_insts ++
      [mk_inst owner_st.cs_next_id JMP [Label (FST labels)] []]|>
Proof
  simp_tac bool_ss [abi_encode_array_header_shape] >> strip_tac >>
  gvs[fn_has_code_def, emitted_blocks_def, DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem abi_encode_array_suffix_code:
  abi_decode_loop_suffix ip (Var iv) hdr exit_lbl body_end = ((),exit_st) /\
  fn_has_code body_end exit_st func ==>
  exit_st.cs_next_var = body_end.cs_next_var+1 /\ exit_st.cs_next_id = body_end.cs_next_id+3 /\
  exit_st.cs_current_bb = exit_lbl /\ exit_st.cs_current_insts = [] /\
  lookup_block body_end.cs_current_bb func.fn_blocks = SOME
    <|bb_label := body_end.cs_current_bb; bb_instructions := body_end.cs_current_insts ++
      abi_decode_backedge_insts body_end.cs_next_id iv
        (STRING #"%" (toString body_end.cs_next_var)) ip hdr|>
Proof
  simp_tac bool_ss [abi_decode_loop_suffix_shape] >> strip_tac >>
  gvs[abi_decode_loop_suffix_state_def, fn_has_code_def, emitted_blocks_def]
QED

Theorem abi_encode_array_addresses_head:
  abi_encode_array_addresses ip src dst asz msz st = (coords,prepared) ==>
  prepared.cs_blocks = st.cs_blocks /\ prepared.cs_current_bb = st.cs_current_bb /\
  ?rest. prepared.cs_current_insts = st.cs_current_insts ++
    mk_inst st.cs_next_id MLOAD [ip] [STRING #"%" (toString st.cs_next_var)] :: rest
Proof
  simp[abi_encode_array_addresses_def, abi_decode_array_head_setup_def, abi_decode_indexed_coordinates_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >> simp[]
QED

Theorem abi_encode_array_static_entry_phi:
  abi_encoder_static_leaf ei /\ abi_encode_array_static_body ip src dst ei asz msz st = (idx,body_end) /\
  fn_has_code st body_end func /\ st.cs_current_insts = [] ==>
  ?bb. lookup_block st.cs_current_bb func.fn_blocks = SOME bb /\
    phi_prefix_length bb.bb_instructions = 0
Proof
  strip_tac >> drule_all abi_encode_array_static_body_context >> strip_tac >>
  drule abi_encode_array_addresses_head >> strip_tac >>
  qpat_assum `fn_has_code st prepared func`
    (mp_tac o CONJUNCT2 o PURE_REWRITE_RULE [fn_has_code_def]) >> strip_tac >>
  qexists_tac `bb` >> gvs[IS_PREFIX_APPEND, phi_prefix_length_def, mk_inst_def]
QED

Theorem abi_encode_array_dynamic_entry_phi:
  abi_encode_array_dynamic_body ip dyn_ptr src dst ei asz msz st = (idx,body_end) /\
  fn_has_code st body_end func /\ st.cs_current_insts = [] ==>
  ?bb. lookup_block st.cs_current_bb func.fn_blocks = SOME bb /\
    phi_prefix_length bb.bb_instructions = 0
Proof
  strip_tac >> drule_all abi_encode_array_dynamic_body_context >> strip_tac >>
  drule abi_encode_array_addresses_head >> strip_tac >>
  qpat_assum `fn_has_code st addressed func`
    (mp_tac o CONJUNCT2 o PURE_REWRITE_RULE [fn_has_code_def]) >> strip_tac >>
  qexists_tac `bb` >> gvs[IS_PREFIX_APPEND, phi_prefix_length_def, mk_inst_def]
QED

Theorem abi_encode_array_exit_phi:
  (abi_encode_array_static_exit src asz exit_st = (out,final) /\
   fn_has_code exit_st final func /\ exit_st.cs_current_insts = [] ==>
   !bb. lookup_block exit_st.cs_current_bb func.fn_blocks = SOME bb ==>
     phi_prefix_length bb.bb_instructions = 0) /\
  (abi_encode_array_dynamic_exit src dyn_ptr exit_st = (out,final) /\
   fn_has_code exit_st final func /\ exit_st.cs_current_insts = [] ==>
   !bb. lookup_block exit_st.cs_current_bb func.fn_blocks = SOME bb ==>
     phi_prefix_length bb.bb_instructions = 0)
Proof
  conj_tac >> simp_tac bool_ss [abi_encode_array_static_exit_def, abi_encode_array_dynamic_exit_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  gvs[fn_has_code_def, IS_PREFIX_APPEND, phi_prefix_length_def, mk_inst_def]
QED

Theorem abi_encode_array_exit_code:
  (abi_encode_array_static_exit src asz exit_st = (out,final) /\ cs_extends exit_st final /\
   fn_has_code exit_st final func /\ exit_st.cs_current_insts = [] ==>
   ?bb. lookup_block exit_st.cs_current_bb func.fn_blocks = SOME bb /\
     phi_prefix_length bb.bb_instructions = 0) /\
  (abi_encode_array_dynamic_exit src dyn_ptr exit_st = (out,final) /\ cs_extends exit_st final /\
   fn_has_code exit_st final func /\ exit_st.cs_current_insts = [] ==>
   ?bb. lookup_block exit_st.cs_current_bb func.fn_blocks = SOME bb /\
     phi_prefix_length bb.bb_instructions = 0)
Proof
  conj_tac >> strip_tac >> drule_all abi_decoder_code_entry_prefix >> strip_tac >>
  qexists_tac `bb` >> asm_simp_tac bool_ss [] >>
  FIRST [drule_all (cj 1 abi_encode_array_exit_phi), drule_all (cj 2 abi_encode_array_exit_phi)] >>
  asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_ARRAY_LOOP_LAYOUT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder array loop layout not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderArrayLoopLayout");
