(* Finite actual loop execution and its scalar exit return the complete ABI array. *)
Theory abiEncoderArrayLoopResult
Ancestors
  abiEncoderArrayFiniteLoop abiEncoderArrayExit abiEncoderArrayLoopCode
  abiEncoderArrayLoopInvariant abiEncoderArrayCode abiEncoderAdmissible abiEncoderCorrect
  abiDecoderEffect abiDecoderContract abiDecoderLoop fragExec compileEnv valueEncoding
  contractABI venomState words list arithmetic

Theorem abi_encoder_array_loop_result:
  (if active then abi_encoder_correct ei else abi_encoder_static_leaf ei) /\
  (if active then abi_encode_array_dynamic_body ip dyn_ptr src dst ei asz msz body_st = (idx,body_end)
    else abi_encode_array_static_body ip src dst ei asz msz body_st = (idx,body_end)) /\
  abi_encoder_array_loop_code func owner_st body_st body_end exit_st ip count_op labels /\
  (if active then abi_encode_array_dynamic_exit src dyn_ptr exit_st = (out,final)
    else abi_encode_array_static_exit src asz exit_st = (out,final)) /\
  fn_has_code exit_st final func /\ body_end.cs_next_id+3 <= hi /\ hi <= last /\
  body_end.cs_next_var+1 <= limit_st.cs_next_var /\ final.cs_next_var <= limit_st.cs_next_var /\
  abi_encoder_array_loop_inv ei asz msz active ty avs owner_st limit_st src dst ip dyn_ptr
    site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op (FST labels) i origin initial ==>
  ?actual.
    mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) actual.vs_memory = enc (Array NONE ty) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
    abi_decoder_effect first last site hi owner_st.cs_next_var limit_st d output_size b cap origin actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_array_finite_loop >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial prepared` >>
  qpat_assum `abi_encoder_array_loop_code _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_array_loop_code_def]) >>
  `owner_st.cs_next_var <= exit_st.cs_next_var /\ owner_st.cs_next_id <= last` by decide_tac >>
  mp_tac (Q.INST [`initial` |-> `prepared:venom_state`, `label` |-> `SND (SND (labels:string # string # string))`,
    `st` |-> `exit_st`] abi_encoder_array_loop_scalar_exit) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  irule abi_decode_sim_trans >> qexists_tac `prepared` >> asm_simp_tac bool_ss []
QED
