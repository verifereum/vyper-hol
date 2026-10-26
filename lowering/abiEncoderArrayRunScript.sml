(* Compose actual parent initialization, selected full loop, and parent finish. *)
Theory abiEncoderArrayRun
Ancestors
  abiEncoderArrayContext abiEncoderArrayCompose abiEncoderArrayParentPrepare abiEncoderComplexCompose
  abiEncoderArrayMemory abiEncoderChildInputs abiEncoderMembersDefs abiEncoderCorrect abiEncoderAdmissible
  abiDecoderEffect abiDecoderContract abiDecoderLoop fragExec compileEnv
  valueEncoding contractABI venomState words list arithmetic

Theorem abi_encoder_array_run:
  (if active then abi_encoder_correct ei else abi_encoder_static_leaf ei) /\
  compile_abi_encode_to_buf dst src (AbiDynArray ei asz msz active) start = (out,final) /\
  fn_has_code start final func /\
  abi_encoder_buffer_pre (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
    start src dst sb source_cap d output_size b cap initial /\
  LENGTH (enc (Array NONE ty) (ListV avs)) <= output_size /\
  abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\ final.cs_next_id <= last /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = start.cs_current_bb /\ initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual.
    mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) actual.vs_memory = enc (Array NONE ty) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
    abi_decoder_effect first last start.cs_next_id final.cs_next_id start.cs_next_var
      limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> drule_all abi_encode_array_context >> strip_tac >>
  `loop_st.cs_next_id <= last /\ loop_end.cs_next_id <= last /\
   loop_st.cs_next_var <= limit_st.cs_next_var /\ loop_end.cs_next_var <= limit_st.cs_next_var /\
   start.cs_next_id < loop_st.cs_next_id /\ start.cs_next_id < final.cs_next_id /\
   first <= loop_st.cs_next_id /\ start.cs_next_var <= loop_st.cs_next_var /\
   loop_end.cs_next_id <= final.cs_next_id` by decide_tac >>
  qpat_assum `abi_encoder_buffer_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (assume_tac o List.last o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_buffer_pre_def]) >>
  mp_tac (Q.INST [`st` |-> `start`, `hi` |-> `loop_st.cs_next_id`] abi_encoder_array_parent_prepare) >>
  impl_tac >- asm_simp_tac (srw_ss()) [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial ready` >>
  `fresh_vars_wrt limit_st ready /\ abi_decoder_budget first last b cap ready` by fs[abi_decoder_effect_def] >>
  mp_tac (Q.INST [`count_op` |-> `SND (ops:operand # operand)`, `start` |-> `loop_st`,
    `out` |-> `size_op`, `final` |-> `loop_end`, `initial` |-> `ready:venom_state`,
    `hi` |-> `loop_end.cs_next_id`] abi_encoder_array_selected_loop) >>
  impl_tac >- asm_simp_tac (srw_ss()) [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func ready encoded` >>
  mp_tac (Q.INST [`parent_ptr` |-> `FST (ops:operand # operand)`, `parent_site` |-> `start.cs_next_id`,
    `parent_slot` |-> `slot:num`, `len` |-> `LENGTH (enc (Array NONE ty) (ListV avs))`,
    `bytes` |-> `enc (Array NONE ty) (ListV avs)`] abi_encoder_array_finish_protected) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `abi_decoder_effect first last start.cs_next_id loop_end.cs_next_id loop_st.cs_next_var
    limit_st d output_size b cap ready encoded` by
    (irule abi_decoder_effect_widen >>
     qexistsl_tac [`d`, `loop_end.cs_next_id`, `loop_st.cs_next_id`, `loop_st.cs_next_var`, `output_size`] >>
     asm_simp_tac (srw_ss()) [] >> decide_tac) >>
  mp_tac (Q.INST [`st` |-> `start`, `prepared` |-> `loop_st`, `middle` |-> `loop_end`,
    `end_st` |-> `final`, `sz` |-> `output_size:num`] abi_encoder_complex_compose) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_ARRAY_RUN_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder complete array execution not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderArrayRun");
