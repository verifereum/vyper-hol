(* Syntax facts for the generic array setup and its recursive child's blocks. *)
Theory abiDecoderArraySetupCode
Ancestors
  abiDecoderPhi abiDecoderLoopSetup abiDecoderIndexedAddress abiDecoderArrayBody
  abiDecoderContract abiDecoderDynamic abiDecoderExecution abiEncoder
  fragExec exprLoweringProps emitHelperProps compileEnv emitHelper
  venomState venomExecSemantics venomInst list rich_list arithmetic words

Theorem abi_decoder_array_setup_head:
  abi_decode_array_element_setup ip src dst opc hi di asz msz st = (ops,middle) ==>
  FST ops = Var (STRING #"%" (toString st.cs_next_var)) /\
  middle.cs_blocks = st.cs_blocks /\ middle.cs_current_bb = st.cs_current_bb /\
  st.cs_next_id < middle.cs_next_id /\
  ?rest. middle.cs_current_insts = st.cs_current_insts ++
    mk_inst st.cs_next_id MLOAD [ip] [STRING #"%" (toString st.cs_next_var)] :: rest
Proof
  Cases_on `dec_info_needs_offset di` >> Cases_on `hi = Lit 0w` >>
  simp[abi_decode_array_element_setup_def, abi_decode_indexed_address_def,
    compile_abi_decode_dyn_elem_ptr_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[] >> pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >> simp[]
QED

Theorem abi_decoder_array_child_phi:
  abi_decode_array_element_setup ip src dst opc hi di asz msz st = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) opc hi di middle = ((),end_st) /\
  abi_decode_source_opcode opc /\ st.cs_current_insts = [] ==>
  phi_prefix_length end_st.cs_current_insts = 0 /\
  ?new. end_st.cs_blocks = new ++ st.cs_blocks /\
    EVERY (\bb. phi_prefix_length bb.bb_instructions = 0) new
Proof
  strip_tac >> drule abi_decoder_array_setup_head >> strip_tac >>
  `phi_prefix_length middle.cs_current_insts = 0` by
    simp[phi_prefix_length_def, mk_inst_def] >>
  drule_all abi_decoder_to_buf_phi >> simp[]
QED

Theorem abi_decoder_array_child_end_phi:
  abi_decode_array_element_setup ip src dst opc hi di asz msz st = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) opc hi di middle = ((),end_st) /\
  abi_decode_source_opcode opc /\ st.cs_current_insts = [] /\
  bb.bb_instructions = end_st.cs_current_insts ++
    abi_decode_backedge_insts end_st.cs_next_id iv nv ip hdr ==>
  phi_prefix_length bb.bb_instructions = 0
Proof
  strip_tac >> drule_all abi_decoder_array_child_phi >> strip_tac >>
  asm_rewrite_tac [] >> irule abi_decoder_phi_append >>
  simp[abi_decode_backedge_insts_def, phi_prefix_length_def, mk_inst_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_ARRAY_SETUP_CODE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI array setup syntax not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderArraySetupCode");
