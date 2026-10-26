(* Whole-loop code containment supplies each real compiler phase's containing code. *)
Theory abiEncoderArrayLoopContext
Ancestors
  abiEncoderArrayTrace abiEncoderArrayPhaseAppend abiEncoderArrayPhases abiEncoderArrayCode
  abiDecoderIndexInit abiDecoderLoopEmit abiEncoder fragExec compileEnv list

Theorem abi_encoder_five_phase_code:
  cs_extends start owner_st /\ cs_extends owner_st body_st /\ cs_extends body_st body_end /\
  cs_extends body_end exit_st /\ cs_extends exit_st final /\ fn_has_code start final func ==>
  fn_has_code start owner_st func /\ fn_has_code owner_st body_st func /\
  fn_has_code body_st body_end func /\ fn_has_code body_end exit_st func /\ fn_has_code exit_st final func
Proof
  strip_tac >>
  `cs_extends body_end final` by
    (irule cs_extends_trans >> qexists_tac `exit_st` >> asm_simp_tac bool_ss []) >>
  `cs_extends body_st final` by
    (irule cs_extends_trans >> qexists_tac `body_end` >> asm_simp_tac bool_ss []) >>
  `cs_extends owner_st final` by
    (irule cs_extends_trans >> qexists_tac `body_st` >> asm_simp_tac bool_ss []) >>
  mp_tac (Q.SPECL [`start`, `owner_st`, `final`, `func`] fn_has_code_split) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.SPECL [`owner_st`, `body_st`, `final`, `func`] fn_has_code_split) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.SPECL [`body_st`, `body_end`, `final`, `func`] fn_has_code_split) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.SPECL [`body_end`, `exit_st`, `final`, `func`] fn_has_code_split) >>
  impl_tac >- asm_simp_tac bool_ss [] >> asm_simp_tac bool_ss []
QED

Theorem abi_encode_array_static_loop_context:
  compile_abi_encode_dyn_static_loop dst src ei asz msz count_op start = (out,final) /\
  fn_has_code start final func ==>
  ?ip owner_st labels body_st idx body_end exit_st.
    abi_decode_index_init start = (ip,owner_st) /\
    abi_encode_array_header ip count_op owner_st = (labels,body_st) /\
    abi_encode_array_static_body ip src dst ei asz msz body_st = (idx,body_end) /\
    abi_decode_loop_suffix ip idx (FST labels) (SND (SND labels)) body_end = ((),exit_st) /\
    abi_encode_array_static_exit src asz exit_st = (out,final) /\
    cs_extends start owner_st /\ cs_extends owner_st body_st /\ cs_extends body_st body_end /\
    cs_extends body_end exit_st /\ cs_extends exit_st final /\
    fn_has_code start owner_st func /\ fn_has_code owner_st body_st func /\
    fn_has_code body_st body_end func /\ fn_has_code body_end exit_st func /\ fn_has_code exit_st final func
Proof
  strip_tac >> drule abi_encode_array_static_loop_trace >> strip_tac >>
  mp_tac (Q.INST [`hdr` |-> `FST (labels:string # string # string)`,
    `exit_lbl` |-> `SND (SND (labels:string # string # string))`] abi_encode_array_phase_append) >> strip_tac >>
  imp_res_tac abi_encoder_appends_result >>
  drule_all abi_encoder_five_phase_code >> strip_tac >>
  qexistsl_tac [`ip`, `owner_st`, `labels`, `body_st`, `idx`, `body_end`, `exit_st`] >>
  asm_simp_tac bool_ss []
QED

Theorem abi_encode_array_dynamic_loop_context:
  compile_abi_encode_dyn_loop dst src ei asz msz count_op start = (out,final) /\
  fn_has_code start final func ==>
  ?ptrs owner_st labels body_st idx body_end exit_st.
    abi_encode_array_dynamic_init count_op asz start = (ptrs,owner_st) /\
    abi_encode_array_header (FST ptrs) count_op owner_st = (labels,body_st) /\
    abi_encode_array_dynamic_body (FST ptrs) (SND ptrs) src dst ei asz msz body_st = (idx,body_end) /\
    abi_decode_loop_suffix (FST ptrs) idx (FST labels) (SND (SND labels)) body_end = ((),exit_st) /\
    abi_encode_array_dynamic_exit src (SND ptrs) exit_st = (out,final) /\
    cs_extends start owner_st /\ cs_extends owner_st body_st /\ cs_extends body_st body_end /\
    cs_extends body_end exit_st /\ cs_extends exit_st final /\
    fn_has_code start owner_st func /\ fn_has_code owner_st body_st func /\
    fn_has_code body_st body_end func /\ fn_has_code body_end exit_st func /\ fn_has_code exit_st final func
Proof
  strip_tac >> drule abi_encode_array_dynamic_loop_trace >> strip_tac >>
  mp_tac (Q.INST [`ip` |-> `FST (ptrs:operand # operand)`, `dyn_ptr` |-> `SND (ptrs:operand # operand)`,
    `hdr` |-> `FST (labels:string # string # string)`,
    `exit_lbl` |-> `SND (SND (labels:string # string # string))`] abi_encode_array_phase_append) >> strip_tac >>
  imp_res_tac abi_encoder_appends_result >>
  drule_all abi_encoder_five_phase_code >> strip_tac >>
  qexistsl_tac [`ptrs`, `owner_st`, `labels`, `body_st`, `idx`, `body_end`, `exit_st`] >>
  asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_ARRAY_LOOP_CONTEXT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder array loop context not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderArrayLoopContext");
