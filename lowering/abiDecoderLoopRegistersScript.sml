(* Repeated header execution overwrites only its four generated temporaries. *)
Theory abiDecoderLoopRegisters
Ancestors
  abiDecoderArrayInvariant abiDecoderArrayBackedge abiDecoderReentryAllocation abiDecoderReentry
  abiDecoderExecution abiDecoderContract emitHelperProps exprLoweringProps
  compileEnv venomState finite_map words arithmetic

Theorem abi_decoder_generated_update:
  next < limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  fresh_vars_wrt limit_st (update_var (STRING #"%" (toString next)) w s) /\
  (!op. abi_decoder_operand_live next op ==>
    eval_operand op (update_var (STRING #"%" (toString next)) w s) = eval_operand op s)
Proof
  strip_tac >>
  mp_tac (Q.INST [`t` |-> `update_var (STRING #"%" (toString (next:num))) (w:bytes32) s`]
    abi_decoder_register_update) >> simp[update_var_def]
QED

Theorem abi_decoder_generated_update_fresh:
  next < limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  fresh_vars_wrt limit_st (update_var (STRING #"%" (toString next)) w s)
Proof
  strip_tac >> drule_all abi_decoder_generated_update >> simp[]
QED

Theorem abi_decoder_generated_update_operand:
  abi_decoder_operand_live next op ==>
  eval_operand op (update_var (STRING #"%" (toString next)) w s) = eval_operand op s
Proof
  strip_tac >>
  `op <> Var (STRING #"%" (toString next))` by
    (mp_tac (Q.INST [`first` |-> `next:num`] abi_decoder_live_excludes_output) >> simp[]) >>
  Cases_on `op` >> gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem abi_decoder_header_registers:
  next + 4 <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  fresh_vars_wrt limit_st
    (abi_decode_header_state (STRING #"%" (toString next))
      (STRING #"%" (toString (next+1))) (STRING #"%" (toString (next+2)))
      (STRING #"%" (toString (next+3))) i ncount s) /\
  (!op. abi_decoder_operand_live next op ==>
    eval_operand op
      (abi_decode_header_state (STRING #"%" (toString next))
        (STRING #"%" (toString (next+1))) (STRING #"%" (toString (next+2)))
        (STRING #"%" (toString (next+3))) i ncount s) = eval_operand op s)
Proof
  strip_tac >>
  `next < limit_st.cs_next_var /\ next+1 < limit_st.cs_next_var /\
   next+2 < limit_st.cs_next_var /\ next+3 < limit_st.cs_next_var` by decide_tac >>
  conj_tac
  >- asm_simp_tac bool_ss [abi_decode_header_state_def, abi_decoder_generated_update_fresh] >>
  gen_tac >> strip_tac >>
  `next <= next+1 /\ next <= next+2 /\ next <= next+3` by simp[] >>
  imp_res_tac abi_decoder_operand_live_mono >>
  asm_simp_tac bool_ss [abi_decode_header_state_def, abi_decoder_generated_update_operand]
QED

Theorem abi_decoder_header_array_memory[simp]:
  abi_decoder_array_memory opc aty avs tv vs sb d j
    (abi_decode_header_state iv cv cmp done i ncount s) <=>
  abi_decoder_array_memory opc aty avs tv vs sb d j s
Proof
  simp[abi_decode_header_state_def]
QED

Theorem abi_decoder_operand_jump[simp]:
  eval_operand op (jump_to lbl s) = eval_operand op s
Proof
  Cases_on `op` >> simp[eval_operand_def, jump_to_def, lookup_var_def]
QED

Theorem abi_decoder_fresh_jump[simp]:
  fresh_vars_wrt st (jump_to lbl s) <=> fresh_vars_wrt st s
Proof
  simp[fresh_vars_wrt_def, jump_to_def]
QED

Theorem abi_decoder_array_header:
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  abi_decoder_array_memory opc aty avs tv vs sb d j s /\ LENGTH avs = LENGTH vs /\
  sb + LENGTH (enc (Array NONE aty) (ListV avs)) < dimword (:256) /\
  LENGTH vs < dimword (:256) /\ abi_decode_source_opcode opc /\
  eval_operand ip s = SOME p /\ mload (w2n p) s = n2w j /\
  eval_operand src s = SOME (n2w sb) /\
  abi_decoder_operand_live next src /\ abi_decoder_operand_live next ip /\
  next + 4 <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?result_st. exec_block fuel ctx
    <|bb_label := hdr; bb_instructions :=
      abi_decode_header_insts id ip src opc (STRING #"%" (toString next))
        (STRING #"%" (toString (next+1))) (STRING #"%" (toString (next+2)))
        (STRING #"%" (toString (next+3))) body_lbl exit_lbl|> s = OK result_st /\
    abi_decoder_array_memory opc aty avs tv vs sb d j result_st /\
    result_st.vs_current_bb = (if j < LENGTH vs then body_lbl else exit_lbl) /\
    result_st.vs_inst_idx = 0 /\ ~result_st.vs_halted /\
    eval_operand ip result_st = SOME p /\ eval_operand src result_st = SOME (n2w sb) /\
    fresh_vars_wrt limit_st result_st /\
    (!op. abi_decoder_operand_live next op ==>
      eval_operand op result_st = eval_operand op s) /\
    result_st.vs_allocas = s.vs_allocas /\ result_st.vs_alloca_next = s.vs_alloca_next /\
    result_st = jump_to (if j < LENGTH vs then body_lbl else exit_lbl)
      (abi_decode_header_state (STRING #"%" (toString next))
        (STRING #"%" (toString (next+1))) (STRING #"%" (toString (next+2)))
        (STRING #"%" (toString (next+3))) j (LENGTH vs) s)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_array_memory_count >> strip_tac >>
  `j <= LENGTH vs` by fs[abi_decoder_array_memory_def, Excl "enc_def"] >>
  `src <> Var (STRING #"%" (toString next))` by
    (mp_tac (Q.INST [`first` |-> `next:num`, `op` |-> `src:operand`]
       abi_decoder_live_excludes_output) >> simp[]) >>
  `STRING #"%" (toString (next:num)) <> STRING #"%" (toString (next+1))` by simp[] >>
  qabbrev_tac `result_st = jump_to (if j < LENGTH vs then body_lbl else exit_lbl)
    (abi_decode_header_state (STRING #"%" (toString next))
      (STRING #"%" (toString (next+1))) (STRING #"%" (toString (next+2)))
      (STRING #"%" (toString (next+3))) j (LENGTH vs) s)` >>
  drule_all abi_decode_header_control >> strip_tac >>
  drule_all abi_decoder_header_registers >> strip_tac >>
  `!op. abi_decoder_operand_live next op ==>
    eval_operand op result_st = eval_operand op s` by
    asm_simp_tac bool_ss [Abbr`result_st`, abi_decoder_operand_jump] >>
  `eval_operand ip result_st = SOME p /\ eval_operand src result_st = SOME (n2w sb)`
    by metis_tac[] >>
  qexists_tac `result_st` >>
  asm_simp_tac (srw_ss()) [Abbr`result_st`, Excl "enc_def"] >>
  simp[jump_to_def, abi_decode_header_state_def, update_var_def]
QED
