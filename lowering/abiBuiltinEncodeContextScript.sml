(* Actual wrapper phase code containment, counter bounds and live outputs. *)
Theory abiBuiltinEncodeContext
Ancestors
  abiBuiltinEncodeCode abiBuiltinAllocation abiEncoderAppend abiEncoderCounters abiEncoderResultLive
  abiDecoderReentry abiDecoderAppend abiDecoderContract fragExec compileEnv emitHelperProps
  exprLoweringProps venomInst words list arithmetic

Theorem abi_builtin_encode_setup_outputs:
  abi_builtin_encode_setup method_id_opt maxlen st = (ops,ready) ==>
  FST ops = Var (STRING #"%" (toString st.cs_next_var)) /\
  SND ops = Var (STRING #"%" (toString (st.cs_next_var+1)))
Proof
  strip_tac >> drule abi_builtin_encode_setup_trace >> strip_tac >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >> gvs[]
QED

Theorem abi_builtin_encode_setup_live:
  abi_builtin_encode_setup method_id_opt maxlen st = (ops,ready) ==>
  abi_decoder_operand_live ready.cs_next_var (FST ops) /\
  abi_decoder_operand_live ready.cs_next_var (SND ops)
Proof
  strip_tac >> drule abi_builtin_encode_setup_outputs >> strip_tac >>
  drule abi_builtin_encode_setup_shape >> strip_tac >>
  Cases_on `method_id_opt` >>
  asm_simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
  rpt strip_tac >> decide_tac
QED

Theorem abi_builtin_encode_code:
  abi_builtin_encode_setup method_id_opt maxlen st = (ops,ready) /\
  compile_abi_encode_to_buf (SND ops) src info ready = (len,body_end) /\
  abi_builtin_encode_finish (FST ops) len mid_size body_end = ((),final) /\
  fn_has_code st final func ==>
  fn_has_code st ready func /\ fn_has_code ready final func /\
  fn_has_code ready body_end func /\ fn_has_code body_end final func /\
  ready.cs_blocks = st.cs_blocks /\ final.cs_blocks = body_end.cs_blocks /\
  final.cs_current_bb = body_end.cs_current_bb /\
  st.cs_next_var <= ready.cs_next_var /\ ready.cs_next_var <= body_end.cs_next_var /\
  body_end.cs_next_var <= final.cs_next_var /\
  st.cs_next_id <= ready.cs_next_id /\ ready.cs_next_id <= body_end.cs_next_id /\
  body_end.cs_next_id <= final.cs_next_id /\
  abi_decoder_operand_live body_end.cs_next_var (FST ops) /\
  abi_decoder_operand_live body_end.cs_next_var len
Proof
  strip_tac >> drule abi_builtin_encode_setup_shape >> strip_tac >>
  drule abi_builtin_encode_finish_shape >> strip_tac >>
  drule abi_encoder_counters >> strip_tac >>
  drule abi_builtin_encode_setup_live >> strip_tac >>
  drule abi_encode_result_live >> strip_tac >>
  `cs_extends st ready /\ cs_extends body_end final` by
    (conj_tac >> irule cs_extends_same_block >> asm_simp_tac bool_ss []) >>
  drule cs_extends_abi_encode >> strip_tac >>
  `cs_extends ready final` by
    (irule cs_extends_trans >> qexists_tac `body_end` >> asm_simp_tac bool_ss []) >>
  mp_tac (Q.SPECL [`st`, `ready`, `final`, `func`] fn_has_code_split) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.SPECL [`ready`, `body_end`, `final`, `func`] fn_has_code_split) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `abi_decoder_operand_live body_end.cs_next_var (FST ops)` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `ready.cs_next_var` >>
     asm_simp_tac bool_ss []) >>
  Cases_on `method_id_opt` >> asm_simp_tac (srw_ss()) [] >> decide_tac
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_BUILTIN_ENCODE_CONTEXT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI builtin encoder context not kernel closed: " ^ n)
  end) (DB.thms "abiBuiltinEncodeContext");
