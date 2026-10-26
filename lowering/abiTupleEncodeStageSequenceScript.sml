(* Execute allocation and complete tuple construction, including site reuse. *)
Theory abiTupleEncodeStageSequence
Ancestors
  abiTupleEncodeStageCode abiTupleEncodeSequence abiTupleEncodeResult abiTupleEncodeMemory
  abiTupleEncodeInput abiTupleProps abiBuiltinAllocationState abiBuiltinAllocation
  abiDecoderReentry abiDecoderContract abiDecoderFrameCompose abiDecoderGuards
  compileEnv emitHelperProps exprLoweringProps venomState venomExecSemantics
  finite_map words list arithmetic

Theorem abi_tuple_encode_stage_sequence:
  compile_alloc_buffer (abi_tuple_bytes ce xs) st = (source_buf,allocated) /\
  compile_store_abi_tuple ce source_buf.buf_operand 0 xs allocated = ((),staged) /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ sb = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (sb,abi_tuple_bytes ce xs)) /\
  sb+abi_tuple_bytes ce xs < dimword (:256) /\
  abi_tuple_encode_inputs sf ce xs ats avs st.cs_next_var sb (sb+abi_tuple_bytes ce xs) initial /\
  staged.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st staged) initial = OK actual /\ inst_extends st staged /\
    eval_operand source_buf.buf_operand actual = SOME (n2w sb) /\
    abi_tuple_encode_memory sf ce xs ats avs sb actual.vs_memory /\
    fresh_vars_wrt limit_st actual /\ abi_decode_frame sb (abi_tuple_bytes ce xs) initial actual /\
    actual.vs_allocas = (abi_builtin_allocate_state st.cs_next_id (abi_tuple_bytes ce xs) initial).vs_allocas /\
    actual.vs_alloca_next = (abi_builtin_allocate_state st.cs_next_id (abi_tuple_bytes ce xs) initial).vs_alloca_next /\
    actual.vs_halted = initial.vs_halted /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_tuple_encode_stage_shape >> strip_tac >> drule abi_tuple_encode_alloc_shape >> strip_tac >>
  `abi_tuple_bytes ce xs < dimword (:256) /\ allocated.cs_next_var <= limit_st.cs_next_var /\
   st.cs_next_var <= allocated.cs_next_var` by decide_tac >>
  drule_all abi_builtin_alloc_buffer_frame >> strip_tac >>
  rename1 `abi_builtin_allocation_frame st.cs_next_var st.cs_next_id _ initial addressed` >>
  qpat_assum `abi_builtin_allocation_frame _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_allocation_frame_def]) >>
  `abi_tuple_encode_inputs sf ce xs ats avs allocated.cs_next_var sb (sb+abi_tuple_bytes ce xs) addressed` by
    (mp_tac (Q.INST [`next` |-> `st.cs_next_var`, `later` |-> `allocated.cs_next_var`,
      `lo` |-> `sb:num`, `hi` |-> `sb+abi_tuple_bytes ce xs`, `s` |-> `initial:venom_state`,
      `t` |-> `addressed:venom_state`] (SPEC_ALL abi_tuple_encode_inputs_transport)) >>
     impl_tac >- (asm_simp_tac bool_ss [abi_decode_frame_def] >> decide_tac) >> simp[]) >>
  mp_tac (SIMP_RULE (srw_ss()) [] (Q.INST [`buf` |-> `source_buf.buf_operand`, `off` |-> `0:num`,
    `st` |-> `allocated`, `final` |-> `staged`, `s` |-> `addressed:venom_state`,
    `baddr` |-> `sb:num`, `lo` |-> `sb:num`, `hi` |-> `sb+abi_tuple_bytes ce xs`]
    (SPEC_ALL abi_tuple_encode_sequence))) >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, asm_simp_tac bool_ss [] >> decide_tac]) >>
  strip_tac >> rename1 `abi_tuple_encode_result sf ce xs ats avs allocated staged limit_st sb addressed encoded` >>
  qpat_assum `abi_tuple_encode_result _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_tuple_encode_result_def]) >>
  `eval_operand source_buf.buf_operand encoded = SOME (n2w sb)` by
    (first_x_assum irule >> asm_simp_tac bool_ss []) >>
  `abi_decode_frame sb (abi_tuple_bytes ce xs) initial encoded` by
    (irule abi_decode_frame_trans >> qexists_tac `addressed` >> asm_simp_tac bool_ss [abi_decode_frame_def]) >>
  `run_inst_seq (emitted_insts st staged) initial = OK encoded /\ inst_extends st staged` by
    (mp_tac (Q.INST [`st1` |-> `allocated`, `st2` |-> `staged`, `s` |-> `initial:venom_state`,
      `s1` |-> `addressed:venom_state`, `s2` |-> `encoded:venom_state`] abi_decode_sequence_chain) >>
     asm_simp_tac bool_ss []) >>
  qexists_tac `encoded` >> asm_simp_tac bool_ss [] >> qx_genl_tac [`older`, `older_word`] >> strip_tac >>
  `eval_operand older addressed = SOME older_word` by (first_x_assum irule >> asm_simp_tac bool_ss []) >>
  qpat_x_assum `!op w. abi_decoder_operand_live allocated.cs_next_var op /\ _ ==> _` irule >>
  asm_simp_tac bool_ss [] >> irule abi_decoder_operand_live_mono >>
  qexists_tac `st.cs_next_var` >> asm_simp_tac bool_ss [] >> decide_tac
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_TUPLE_ENCODE_STAGE_SEQUENCE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI tuple staging execution not kernel closed: " ^ n)
  end) (DB.thms "abiTupleEncodeStageSequence");
