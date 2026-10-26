(* Composable execution results for the complete tuple producer. *)
Theory abiTupleEncodeResult
Ancestors
  abiTupleEncodeSlot abiTupleEncodeInput abiTupleEncodeMemory abiTupleProps
  abiEncoderInputFrame abiDecoderReentry abiDecoderContract abiDecoderGuards
  abiDecoderFrameCompose compileEnv emitHelperProps exprLoweringProps
  venomState venomExecSemantics words list arithmetic

Definition abi_tuple_encode_result_def:
  abi_tuple_encode_result sf ce xs ats avs st final limit_st d s t <=>
    run_inst_seq (emitted_insts st final) s = OK t /\ inst_extends st final /\
    abi_tuple_encode_memory sf ce xs ats avs d t.vs_memory /\
    fresh_vars_wrt limit_st t /\ abi_decode_frame d (abi_tuple_bytes ce xs) s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_halted = s.vs_halted /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op t = SOME w)
End

Theorem abi_tuple_encode_result_slot:
  compile_abi_tuple_slot ce buf off op ty st = ((),final) /\
  eval_operand buf s = SOME (n2w baddr) /\ baddr+off < dimword (:256) /\ lo <= hi /\
  abi_tuple_encode_input sf ce ty at av op st.cs_next_var lo hi s /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?actual. abi_tuple_encode_result sf ce [(op,ty)] [at] [av] st final limit_st (baddr+off) s actual
Proof
  strip_tac >> drule_all abi_tuple_encode_slot_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st final) s = OK actual` >> qexists_tac `actual` >>
  asm_simp_tac (srw_ss()) [abi_tuple_encode_result_def, abi_tuple_encode_memory_def, abi_tuple_bytes_def]
QED

Theorem abi_tuple_encode_result_cons:
  abi_tuple_encode_result sf ce [(op,ty)] [at] [av] st middle limit_st d s t /\
  abi_tuple_encode_result sf ce xs ats avs middle final limit_st (d+type_memory_bytes ce ty) t u /\
  st.cs_next_var <= middle.cs_next_var ==>
  abi_tuple_encode_result sf ce ((op,ty)::xs) (at::ats) (av::avs) st final limit_st d s u
Proof
  simp_tac (srw_ss()) [abi_tuple_encode_result_def, abi_tuple_encode_memory_def, abi_tuple_bytes_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_encoder_input (type_to_abi_enc_info sf ce ty) at av d (type_memory_bytes ce ty) u.vs_memory` by
    (irule abi_encoder_input_mem_agree >> qexists_tac `t.vs_memory` >> asm_simp_tac bool_ss [] >>
     irule EQ_SYM >> qpat_x_assum `abi_decode_frame (d+_) _ _ _`
       (MP_TAC o CONJUNCT1 o PURE_REWRITE_RULE [abi_decode_frame_def]) >> disch_then irule >> simp[]) >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  drule_all abi_decode_frame_adjacent >> strip_tac >> asm_simp_tac bool_ss [] >>
  qx_genl_tac [`older`, `older_word`] >> strip_tac >>
  `eval_operand older t = SOME older_word` by (first_x_assum irule >> asm_simp_tac bool_ss []) >>
  qpat_x_assum `!op w. abi_decoder_operand_live middle.cs_next_var op /\ _ ==> _` irule >>
  asm_simp_tac bool_ss [] >> irule abi_decoder_operand_live_mono >>
  qexists_tac `st.cs_next_var` >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_TUPLE_ENCODE_RESULT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI tuple encoder result not kernel closed: " ^ n)
  end) (DB.thms "abiTupleEncodeResult");
