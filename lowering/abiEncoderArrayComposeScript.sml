(* Select a proved actual loop and finish through its protected parent cursor. *)
Theory abiEncoderArrayCompose
Ancestors
  abiEncoderArrayStaticLoop abiEncoderArrayDynamicLoop abiEncoderArrayDynamicInitPrepare
  abiEncoderArrayParentFinish abiEncoderArrayMemory abiEncoderArrayCursor abiEncoderMembersDefs
  abiEncoderCorrect abiEncoderAdmissible abiDecoderEffect abiDecoderContract abiDecoderLoop
  fragExec compileEnv valueEncoding contractABI venomState words list arithmetic

Theorem abi_encoder_array_selected_loop:
  (if active then abi_encoder_correct ei else abi_encoder_static_leaf ei) /\
  (if active then compile_abi_encode_dyn_loop dst src ei asz msz count_op start = (out,final)
    else compile_abi_encode_dyn_static_loop dst src ei asz msz count_op start = (out,final)) /\
  fn_has_code start final func /\
  abi_encoder_array_memory ei asz msz active ty avs start src dst sb source_cap d output_size b cap 0 initial /\
  abi_decoder_operand_live start.cs_next_var count_op /\ eval_operand count_op initial = SOME (n2w (LENGTH avs)) /\
  abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\
  final.cs_next_id <= hi /\ hi <= last /\ final.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = start.cs_current_bb /\ initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual.
    mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) actual.vs_memory = enc (Array NONE ty) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
    abi_decoder_effect first last start.cs_next_id hi start.cs_next_var limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  Cases_on `active` >> simp_tac bool_ss [COND_CLAUSES] >> strip_tac >>
  FIRST [drule_all abi_encoder_array_dynamic_loop, drule_all abi_encoder_array_static_loop] >>
  disch_then (qspec_then `ctx` assume_tac) >> asm_simp_tac bool_ss []
QED

Theorem abi_encoder_array_finish_protected:
  abi_encoder_cursor T parent_ptr parent_site parent_slot first parent_site loop_st 0 ready /\
  abi_decoder_effect first last loop_st.cs_next_id loop_end.cs_next_id loop_st.cs_next_var
    limit_st d output_size b cap ready encoded /\
  loop_st.cs_next_var <= loop_end.cs_next_var /\ loop_st.cs_next_id <= loop_end.cs_next_id /\
  parent_site < loop_st.cs_next_id /\ loop_end.cs_next_id <= last /\ parent_site < final.cs_next_id /\
  abi_encode_array_finish parent_ptr size_op loop_end = (out,final) /\ fn_has_code loop_end final func /\
  eval_operand size_op encoded = SOME (n2w len) /\ abi_decoder_operand_live loop_end.cs_next_var size_op /\
  mem_bytes_at d len encoded.vs_memory = bytes /\ len <= output_size /\ (d+output_size <= b \/ b+cap <= d) /\
  final.cs_next_var <= limit_st.cs_next_var /\ ~encoded.vs_halted /\
  encoded.vs_current_bb = loop_end.cs_current_bb /\ encoded.vs_inst_idx = LENGTH loop_end.cs_current_insts ==>
  ?actual. mem_bytes_at d len actual.vs_memory = bytes /\ eval_operand out actual = SOME (n2w len) /\
    abi_decoder_effect first last parent_site final.cs_next_id loop_end.cs_next_var
      limit_st d output_size b cap encoded actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func encoded actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> `parent_site < last` by decide_tac >>
  `abi_encoder_cursor T parent_ptr parent_site parent_slot first parent_site loop_end 0 encoded` by
    (mp_tac (Q.INST [`active` |-> `T`, `cursor_op` |-> `parent_ptr`, `site` |-> `parent_site:num`,
      `slot` |-> `parent_slot:num`, `lo` |-> `parent_site:num`, `st` |-> `loop_st`,
      `off` |-> `0:num`, `owned_lo` |-> `loop_st.cs_next_id`, `owned_hi` |-> `loop_end.cs_next_id`,
      `prepared` |-> `loop_end`, `initial` |-> `ready:venom_state`,
      `actual` |-> `encoded:venom_state`, `sz` |-> `output_size:num`] abi_encoder_cursor_protected_advance) >>
     impl_tac >- asm_simp_tac (srw_ss()) [] >> asm_simp_tac bool_ss []) >>
  qpat_assum `abi_encoder_cursor T _ _ _ _ _ loop_end _ encoded`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE bool_ss [abi_encoder_cursor_def]) >>
  qpat_assum `abi_decoder_effect _ _ _ _ _ _ _ _ _ _ ready encoded`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_effect_def]) >>
  mp_tac (Q.INST [`st` |-> `loop_end`, `initial` |-> `encoded:venom_state`,
    `site` |-> `parent_site:num`, `slot` |-> `parent_slot:num`, `lo` |-> `parent_site:num`,
    `hi` |-> `final.cs_next_id`] abi_encoder_array_parent_finish) >>
  impl_tac >- (asm_simp_tac (srw_ss()) [] >> gvs[]) >> strip_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_ARRAY_COMPOSE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder array composition not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderArrayCompose");
