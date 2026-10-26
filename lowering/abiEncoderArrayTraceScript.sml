(* Extract the actual initialization, header, body, backedge and exit compiler states. *)
Theory abiEncoderArrayTrace
Ancestors
  abiEncoderArrayPhases abiEncoderArrayCode abiDecoderIndexInit abiDecoderLoopEmit
  abiEncoder compileEnv emitHelper list

Theorem abi_encode_array_static_loop_trace:
  compile_abi_encode_dyn_static_loop dst src ei asz msz count_op start = (out,final) ==>
  ?ip owner_st labels body_st idx body_end exit_st.
    abi_decode_index_init start = (ip,owner_st) /\
    abi_encode_array_header ip count_op owner_st = (labels,body_st) /\
    abi_encode_array_static_body ip src dst ei asz msz body_st = (idx,body_end) /\
    abi_decode_loop_suffix ip idx (FST labels) (SND (SND labels)) body_end = ((),exit_st) /\
    abi_encode_array_static_exit src asz exit_st = (out,final)
Proof
  simp_tac bool_ss [abi_encode_array_static_loop_phases, comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `abi_decode_index_init start = (ip,owner_st)` >>
  rename1 `abi_encode_array_header _ _ owner_st = (labels,body_st)` >>
  rename1 `abi_encode_array_static_body _ _ _ _ _ _ body_st = (idx,body_end)` >>
  rename1 `abi_decode_loop_suffix _ _ _ _ body_end = (ignored,exit_st)` >>
  Cases_on `ignored:unit` >>
  qexistsl_tac [`ip`, `owner_st`, `labels`, `body_st`, `idx`, `body_end`, `exit_st`] >>
  asm_simp_tac bool_ss []
QED

Theorem abi_encode_array_dynamic_loop_trace:
  compile_abi_encode_dyn_loop dst src ei asz msz count_op start = (out,final) ==>
  ?ptrs owner_st labels body_st idx body_end exit_st.
    abi_encode_array_dynamic_init count_op asz start = (ptrs,owner_st) /\
    abi_encode_array_header (FST ptrs) count_op owner_st = (labels,body_st) /\
    abi_encode_array_dynamic_body (FST ptrs) (SND ptrs) src dst ei asz msz body_st = (idx,body_end) /\
    abi_decode_loop_suffix (FST ptrs) idx (FST labels) (SND (SND labels)) body_end = ((),exit_st) /\
    abi_encode_array_dynamic_exit src (SND ptrs) exit_st = (out,final)
Proof
  simp_tac bool_ss [abi_encode_array_dynamic_loop_phases, comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `abi_encode_array_dynamic_init _ _ start = (ptrs,owner_st)` >>
  rename1 `abi_encode_array_header _ _ owner_st = (labels,body_st)` >>
  rename1 `abi_encode_array_dynamic_body _ _ _ _ _ _ _ body_st = (idx,body_end)` >>
  rename1 `abi_decode_loop_suffix _ _ _ _ body_end = (ignored,exit_st)` >>
  Cases_on `ignored:unit` >>
  qexistsl_tac [`ptrs`, `owner_st`, `labels`, `body_st`, `idx`, `body_end`, `exit_st`] >>
  asm_simp_tac bool_ss []
QED

Theorem abi_encode_array_trace:
  compile_abi_encode_to_buf dst src (AbiDynArray ei asz msz dyn) start = (out,final) ==>
  ?ops loop_st size_op loop_end.
    abi_encode_array_prefix src dst start = (ops,loop_st) /\
    (if dyn then compile_abi_encode_dyn_loop dst src ei asz msz (SND ops) loop_st = (size_op,loop_end)
      else compile_abi_encode_dyn_static_loop dst src ei asz msz (SND ops) loop_st = (size_op,loop_end)) /\
    abi_encode_array_finish (FST ops) size_op loop_end = (out,final)
Proof
  simp_tac bool_ss [abi_encode_array_phases, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `abi_encode_array_prefix _ _ start = (ops,loop_st)` >>
  rename1 `abi_encode_array_finish (FST ops) size_op loop_end = (out,final)` >>
  qexistsl_tac [`size_op`, `loop_end`] >> Cases_on `dyn` >> gvs[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_ARRAY_TRACE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder actual array trace not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderArrayTrace");
