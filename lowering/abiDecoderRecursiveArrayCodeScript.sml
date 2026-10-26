(* Extract actual initializer and recursive loop code from array compilation. *)
Theory abiDecoderRecursiveArrayCode
Ancestors
  abiDecoderArrayInitReach abiDecoderArrayInitReentry abiDecoderArrayLoopInit
  abiDecoderLoopEmit abiDecoderRecursiveLoopLayout abiDecoderArraySetupCode abiDecoderLoopCode
  abiDecoderAppend abiDecoderCode abiDecoderCounters abiDecoderContract
  fragExec exprLoweringProps emitHelperProps compileEnv words list arithmetic

Theorem abi_decoder_recursive_loop_end:
  compile_abi_decode_dyn_loop dst src opc hi ei asz msz ip cnt start = ((),final) /\
  abi_decode_source_opcode opc ==>
  start.cs_next_id <= final.cs_next_id /\ start.cs_next_var <= final.cs_next_var /\
  final.cs_current_insts = [] /\
  final.cs_current_bb = fresh_label_output "dec_dyn_exit" (start.cs_next_label+2) /\
  cs_extends start final
Proof
  strip_tac >> drule_all abi_decoder_dyn_loop_code >>
  simp_tac bool_ss [abi_decoder_code_def] >> strip_tac >>
  `start.cs_next_var <= final.cs_next_var` by
    metis_tac[cj 3 abi_decoder_vars_mono_mutual, abi_decoder_vars_mono_def, pairTheory.SND] >>
  `cs_extends start final` by metis_tac[cj 3 cs_appends_abi_decode_mutual, cs_appends_def] >>
  drule abi_decode_dyn_loop_trace >> strip_tac >>
  drule abi_decoder_array_setup_head >> strip_tac >>
  qpat_x_assum `abi_decode_loop_suffix _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  drule abi_decoder_loop_suffix_facts >> strip_tac >>
  qpat_x_assum `abi_decode_loop_prefix _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [abi_decode_loop_prefix_shape] >> strip_tac >> gvs[]
QED

Theorem abi_decoder_recursive_array_code:
  compile_abi_decode_to_buf dst src opc hi (DecDynArray ei asz msz dyn maxn) st = ((),final) /\
  (dyn \/ dec_info_needs_clamp ei) /\ abi_decode_source_opcode opc /\ fn_has_code st final func ==>
  ?setup loop_st.
    abi_decode_array_loop_init dst src opc hi maxn asz st = (setup,loop_st) /\
    compile_abi_decode_dyn_loop dst src opc hi ei asz msz (FST setup) (SND setup)
      loop_st = ((),final) /\
    fn_has_code st loop_st func /\ fn_has_code loop_st final func /\
    st.cs_next_var <= loop_st.cs_next_var /\
    loop_st.cs_next_id <= final.cs_next_id /\ loop_st.cs_next_var <= final.cs_next_var /\
    st.cs_next_id <= loop_st.cs_next_id-2 /\ loop_st.cs_next_id-2 < loop_st.cs_next_id /\
    final.cs_current_insts = [] /\
    final.cs_current_bb = fresh_label_output "dec_dyn_exit" (loop_st.cs_next_label+2)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decode_loop_array_trace >> strip_tac >>
  drule_all abi_decode_array_loop_init_shape >> strip_tac >>
  drule_all abi_decode_array_loop_init_site_bounds >> strip_tac >>
  drule_all abi_decoder_recursive_loop_end >> strip_tac >>
  `cs_extends st loop_st` by (irule cs_extends_same_block >> simp[]) >>
  mp_tac (Q.SPECL [`st`, `loop_st`, `final`, `func`] fn_has_code_split) >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  qexistsl_tac [`setup`, `loop_st`] >> simp[]
QED

Theorem abi_decoder_recursive_array_adds_blocks:
  compile_abi_decode_to_buf dst src opc hi (DecDynArray ei asz msz dyn maxn) st = ((),final) /\
  (dyn \/ dec_info_needs_clamp ei) /\ abi_decode_source_opcode opc /\ fn_has_code st final func ==>
  st.cs_blocks <> final.cs_blocks
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_recursive_array_code >> strip_tac >>
  drule_all abi_decode_array_loop_init_shape >> strip_tac >>
  drule abi_decode_dyn_loop_trace >> strip_tac >>
  rename1 `abi_decode_loop_prefix _ _ _ loop_st = (labels,body_st)` >>
  rename1 `abi_decode_loop_suffix _ _ _ _ child_end = ((),final)` >>
  drule_all abi_decoder_loop_phase_containment >> strip_tac >>
  drule abi_decoder_loop_prefix_facts >> strip_tac >>
  drule abi_decoder_array_setup_head >> strip_tac >>
  qpat_x_assum `abi_decode_loop_suffix _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  drule abi_decoder_loop_suffix_facts >> strip_tac >>
  `?children. child_end.cs_blocks = children ++ body_st.cs_blocks` by fs[cs_extends_def] >>
  `LENGTH st.cs_blocks < LENGTH final.cs_blocks` by
    (asm_simp_tac bool_ss [LENGTH_APPEND, LENGTH] >> decide_tac) >>
  strip_tac >> gvs[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_RECURSIVE_ARRAY_CODE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI recursive array code not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderRecursiveArrayCode");
