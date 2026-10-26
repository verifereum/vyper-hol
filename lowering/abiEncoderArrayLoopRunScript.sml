(* The initial JMP, finite actual iterations and scalar exit form one executable loop. *)
Theory abiEncoderArrayLoopRun
Ancestors
  abiEncoderArrayLoopEntry abiEncoderArrayLoopResult abiEncoderArrayLoopInvariant abiEncoderArrayLoopCode
  abiEncoderArrayMemory abiEncoderMembersDefs abiEncoderArrayCode abiEncoderAdmissible abiEncoderCorrect
  abiDecoderEffect abiDecoderContract abiDecoderLoop fragExec compileEnv
  valueEncoding contractABI venomState venomExecSemantics words list arithmetic

Theorem abi_encoder_array_loop_run:
  (if active then abi_encoder_correct ei else abi_encoder_static_leaf ei) /\
  (if active then abi_encode_array_dynamic_body ip dyn_ptr src dst ei asz msz body_st = (idx,body_end)
    else abi_encode_array_static_body ip src dst ei asz msz body_st = (idx,body_end)) /\
  abi_encoder_array_loop_code func owner_st body_st body_end exit_st ip count_op labels /\
  (if active then abi_encode_array_dynamic_exit src dyn_ptr exit_st = (out,final)
    else abi_encode_array_static_exit src asz exit_st = (out,final)) /\
  fn_has_code exit_st final func /\ body_end.cs_next_id+3 <= hi /\ hi <= last /\
  body_end.cs_next_var+1 <= limit_st.cs_next_var /\ final.cs_next_var <= limit_st.cs_next_var /\
  abi_encoder_array_memory ei asz msz active ty avs owner_st src dst sb source_cap d output_size b cap 0 initial /\
  abi_encoder_cursor T ip site slot first site owner_st 0 initial /\
  abi_encoder_cursor active dyn_ptr cursor_site cursor_slot first site owner_st
    (LENGTH avs*abi_member_head_size ty) initial /\
  (active ==> site < cursor_site) /\ abi_decoder_operand_live owner_st.cs_next_var count_op /\
  eval_operand count_op initial = SOME (n2w (LENGTH avs)) /\
  fresh_vars_wrt limit_st initial /\ abi_decoder_budget first last b cap initial /\
  initial.vs_current_bb = owner_st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH owner_st.cs_current_insts /\ ~initial.vs_halted ==>
  ?actual.
    mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) actual.vs_memory = enc (Array NONE ty) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
    abi_decoder_effect first last site hi owner_st.cs_next_var limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_array_loop_enter >> disch_then (qspecl_then [`hi:num`, `ctx`] strip_assume_tac) >>
  mp_tac (Q.INST [`i` |-> `0:num`, `origin` |-> `initial:venom_state`,
    `initial` |-> `jump_to (FST (labels:string # string # string)) initial`]
    abi_encoder_array_loop_result) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  irule abi_decode_sim_trans >>
  qexists_tac `jump_to (FST (labels:string # string # string)) initial` >> asm_simp_tac bool_ss []
QED
