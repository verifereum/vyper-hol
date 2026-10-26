(* Actual outer array phases have containing code, monotone counters and a live loop result. *)
Theory abiEncoderArrayContext
Ancestors
  abiEncoderArrayTrace abiEncoderArrayPhases abiEncoderArrayCode abiEncoderArrayScalarCode
  abiEncoderArrayPhaseAppend abiEncoderAppend abiEncoderCounters abiDecoderReentry
  abiDecoderContract fragExec compileEnv emitHelperProps emitHelper venomInst words list arithmetic

Theorem abi_encode_array_loop_result_live:
  (compile_abi_encode_dyn_static_loop dst src ei asz msz count_op start = (out,final) ==>
    abi_decoder_operand_live final.cs_next_var out) /\
  (compile_abi_encode_dyn_loop dst src ei asz msz count_op start = (out,final) ==>
    abi_decoder_operand_live final.cs_next_var out)
Proof
  conj_tac >> strip_tac >>
  FIRST [drule abi_encode_array_static_loop_trace, drule abi_encode_array_dynamic_loop_trace] >> strip_tac >>
  FIRST [qpat_x_assum `abi_encode_array_static_exit _ _ _ = _` mp_tac,
    qpat_x_assum `abi_encode_array_dynamic_exit _ _ _ = _` mp_tac] >>
  simp_tac bool_ss [abi_encode_array_static_exit_def, abi_encode_array_dynamic_exit_def,
    comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  qpat_assum `emit_op ADD _ _ = (out,final)`
    (mp_tac o MATCH_MP abi_decoder_operand_live_emit) >> simp[]
QED

Theorem abi_encode_array_loop_bounds:
  (if active then compile_abi_encode_dyn_loop dst src ei asz msz count_op start = (out,final)
    else compile_abi_encode_dyn_static_loop dst src ei asz msz count_op start = (out,final)) ==>
  cs_extends start final /\ start.cs_next_var <= final.cs_next_var /\
  start.cs_next_id <= final.cs_next_id /\ abi_decoder_operand_live final.cs_next_var out
Proof
  strip_tac >> qabbrev_tac `action = if active then compile_abi_encode_dyn_loop dst src ei asz msz count_op
    else compile_abi_encode_dyn_static_loop dst src ei asz msz count_op` >>
  `action start = (out,final)` by (Cases_on `active` >> gvs[Abbr`action`]) >>
  `cs_appends action /\ abi_encoder_counters_mono action` by
    (Cases_on `active` >> simp[Abbr`action`, cj 4 cs_appends_abi_encode_mutual,
      cs_appends_abi_encode_static_loop, cj 4 abi_encoder_counters_mono_mutual,
      abi_encoder_counters_mono_static_loop]) >>
  drule_all abi_encoder_appends_result >> strip_tac >>
  qpat_assum `abi_encoder_counters_mono action`
    (qspec_then `start` mp_tac o PURE_REWRITE_RULE [abi_encoder_counters_mono_def]) >>
  asm_simp_tac (srw_ss()) [] >> strip_tac >>
  Cases_on `active` >> full_simp_tac bool_ss [COND_CLAUSES, Abbr`action`] >>
  FIRST [drule (cj 1 abi_encode_array_loop_result_live), drule (cj 2 abi_encode_array_loop_result_live)] >> simp[]
QED

Theorem abi_encode_array_context:
  compile_abi_encode_to_buf dst src (AbiDynArray ei asz msz active) start = (out,final) /\
  fn_has_code start final func ==>
  ?ops loop_st size_op loop_end.
    abi_encode_array_prefix src dst start = (ops,loop_st) /\
    (if active then compile_abi_encode_dyn_loop dst src ei asz msz (SND ops) loop_st = (size_op,loop_end)
      else compile_abi_encode_dyn_static_loop dst src ei asz msz (SND ops) loop_st = (size_op,loop_end)) /\
    abi_encode_array_finish (FST ops) size_op loop_end = (out,final) /\
    fn_has_code start loop_st func /\ fn_has_code loop_st loop_end func /\ fn_has_code loop_end final func /\
    loop_st.cs_next_var = start.cs_next_var+2 /\ loop_st.cs_next_id = start.cs_next_id+4 /\
    loop_st.cs_next_var <= loop_end.cs_next_var /\ loop_st.cs_next_id <= loop_end.cs_next_id /\
    final.cs_next_var = loop_end.cs_next_var+3 /\ final.cs_next_id = loop_end.cs_next_id+4 /\
    abi_decoder_operand_live loop_end.cs_next_var size_op
Proof
  strip_tac >> drule abi_encode_array_trace >> strip_tac >>
  drule abi_encode_array_prefix_shape >> strip_tac >> drule abi_encode_array_finish_shape >> strip_tac >>
  drule abi_encode_array_loop_bounds >> strip_tac >>
  `cs_extends start loop_st` by
    (irule cs_extends_same_block >> fs[inst_extends_def, rich_listTheory.IS_PREFIX_APPEND]) >>
  `cs_extends loop_end final` by
    (irule cs_extends_same_block >> fs[inst_extends_def, rich_listTheory.IS_PREFIX_APPEND]) >>
  `cs_extends loop_st final` by
    (irule cs_extends_trans >> qexists_tac `loop_end` >> asm_simp_tac bool_ss []) >>
  mp_tac (Q.SPECL [`start`, `loop_st`, `final`, `func`] fn_has_code_split) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.SPECL [`loop_st`, `loop_end`, `final`, `func`] fn_has_code_split) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qexistsl_tac [`ops`, `loop_st`, `size_op`, `loop_end`] >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_ARRAY_CONTEXT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder outer array context not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderArrayContext");
