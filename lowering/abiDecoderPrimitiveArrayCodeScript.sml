(* Extract actual initialization/loop subfragments from primitive array compilation. *)
Theory abiDecoderPrimitiveArrayCode
Ancestors
  abiDecoderArrayInitReach abiDecoderArrayLoopInit abiDecoderLoopEmit
  abiDecoderPrimitiveLoopInvariant abiDecoderPrimitiveLoopLayout
  abiDecoderAppend abiDecoderCode abiDecoderContract fragExec
  exprLoweringProps emitHelperProps compileEnv venomState words list arithmetic

Theorem abi_decoder_primitive_loop_end:
  compile_abi_decode_dyn_loop dst src opc hi (DecPrimWord clamp) 32 32 ip cnt
    start = ((),end_st) /\ abi_decode_source_opcode opc ==>
  start.cs_next_id <= end_st.cs_next_id /\ start.cs_next_var <= end_st.cs_next_var /\
  end_st.cs_current_insts = [] /\
  end_st.cs_current_bb = fresh_label_output "dec_dyn_exit" (start.cs_next_label + 2) /\
  cs_extends start end_st
Proof
  strip_tac >> drule_all abi_decoder_dyn_loop_code >> strip_tac >>
  qpat_assum `abi_decoder_code _ _`
    (assume_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_decoder_code_def]) >>
  `cs_extends start end_st` by metis_tac[cj 3 cs_appends_abi_decode_mutual, cs_appends_def] >>
  drule_all abi_decode_dyn_loop_trace >> strip_tac >>
  `st0.cs_current_insts = [] /\ st0.cs_next_var = start.cs_next_var + 4` by
    gvs[abi_decode_loop_prefix_shape, abi_decode_loop_prefix_state_def] >>
  drule_all abi_decoder_primitive_body_counters >> strip_tac >>
  drule_all abi_decoder_primitive_setup_head >> strip_tac >>
  qpat_x_assum `abi_decode_loop_prefix _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [abi_decode_loop_prefix_shape] >> strip_tac >>
  qpat_x_assum `abi_decode_loop_suffix _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_loop_suffix_shape] >> strip_tac >>
  gvs[abi_decode_loop_suffix_state_def] >> decide_tac
QED

Theorem abi_decoder_primitive_array_code:
  compile_abi_decode_to_buf dst src opc hi
    (DecDynArray (DecPrimWord clamp) 32 32 F maxn) st = ((),end_st) /\
  dec_info_needs_clamp (DecPrimWord clamp) /\ abi_decode_source_opcode opc /\
  fn_has_code st end_st fn ==>
  ?setup loop_st.
    abi_decode_array_loop_init dst src opc hi maxn 32 st = (setup,loop_st) /\
    compile_abi_decode_dyn_loop dst src opc hi (DecPrimWord clamp) 32 32 (FST setup) (SND setup)
      loop_st = ((),end_st) /\
    fn_has_code st loop_st fn /\ fn_has_code loop_st end_st fn /\
    loop_st.cs_next_id <= end_st.cs_next_id /\ loop_st.cs_next_var <= end_st.cs_next_var /\
    end_st.cs_current_insts = [] /\
    end_st.cs_current_bb = fresh_label_output "dec_dyn_exit" (loop_st.cs_next_label + 2)
Proof
  strip_tac >>
  drule_all (SIMP_RULE (srw_ss()) [] (Q.INST [`elem_dyn` |-> `F`] abi_decode_loop_array_trace)) >>
  strip_tac >>
  drule_all abi_decode_array_loop_init_shape >> strip_tac >>
  drule_all abi_decoder_primitive_loop_end >> strip_tac >>
  `cs_extends st loop_st` by (irule cs_extends_same_block >> simp[]) >>
  drule_all fn_has_code_split >> strip_tac >>
  qexistsl_tac [`setup`, `loop_st`] >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_PRIMITIVE_ARRAY_CODE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI primitive array compilation not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderPrimitiveArrayCode");
