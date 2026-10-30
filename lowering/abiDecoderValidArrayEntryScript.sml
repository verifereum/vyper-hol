(* Execute actual dynamic-array address setup and establish the child API. *)
Theory abiDecoderValidArrayEntry
Ancestors
  abiDecoderValidContract abiDecoderValidArraySetupInputs abiDecoderValidArraySetupInputs
  abiDecoderValidArraySetupInputs abiDecoderArraySetupInputs abiDecoderDynamicLoopSetup
  abiDecoderArrayEntry abiDecoderDynamic abiDecoderCoherence abiDecoderTypedContract
  abiDecoderReentry abiDecoderContract abiDecoderLoop abiValidMember abiValidMembers abiEncoder
  fragExec instIdxIndep compileEnv valueEncoding vyperABI vyperValue contractABI venomState
  venomExecSemantics words list arithmetic

Definition abi_decoder_valid_array_entry_def:
  abi_decoder_valid_array_entry ce env sf ty tv bs vs j ready ops opc hi sb d b cap
      next limit_st initial t <=>
    let at = vyper_to_abi_type env ty;
        ao = j * abi_member_head_size at;
        childbs = abi_decode_member_bytes at (DROP 32 bs) (DROP ao (DROP 32 bs));
        off = 32 + abi_decode_member_offset at (DROP 32 bs) ao in
    abi_decoder_valid_pre ce env sf ty tv childbs (EL j vs) ready
      (FST (SND ops)) (SND (SND ops)) opc hi (sb + off)
      (d + 32 + j * type_memory_bytes ce ty) b cap t /\
    eval_operand (FST ops) t = SOME (n2w j) /\ fresh_vars_wrt limit_st t /\
    abi_decoder_address_frame next initial t
End

Theorem abi_decoder_valid_array_entry_inst_idx[simp]:
  abi_decoder_valid_array_entry ce env sf ty tv bs vs j ready ops opc hi sb d b cap
    next limit_st initial (t with vs_inst_idx := ix) <=>
  abi_decoder_valid_array_entry ce env sf ty tv bs vs j ready ops opc hi sb d b cap
    next limit_st initial t
Proof
  simp[abi_decoder_valid_array_entry_def, abi_decoder_valid_pre_def, abi_decoder_ranges_def,
    abi_decode_source_def, abi_decoder_address_frame_def, fresh_vars_wrt_def, eval_op_inst_idx]
QED

Theorem abi_decoder_valid_array_setup_sequence:
  abi_decode_array_element_setup ip src dst opc hi (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) st = (ops,ready) /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) di
    (dec (Array NONE (vyper_to_abi_type env ty)) bs) (ArrayV (DynArrayV vs)) /\
  vyper_decode_valid_enc (Array NONE (vyper_to_abi_type env ty)) bs /\ j < LENGTH vs /\
  is_dynamic (vyper_to_abi_type env ty) /\
  (!elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) /\
  abi_decoder_ranges opc hi src dst sb (LENGTH bs)
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source opc initial) = bs /\
  eval_operand ip initial = SOME p /\ mload (w2n p) initial = n2w j /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  ready.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?prepared. run_inst_seq (emitted_insts st ready) initial = OK prepared /\
    abi_decoder_valid_array_entry ce env sf ty tv bs vs j ready ops opc hi sb d b cap
      st.cs_next_var limit_st initial prepared /\ inst_extends st ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_valid_dynarray_values >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `j < abi_head_word bs` by asm_simp_tac bool_ss [] >>
  drule_all (SIMP_RULE bool_ss [LET_THM] abi_decoder_valid_array_setup_inputs) >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decode_dynamic_element_setup_reentry >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st ready) initial = OK prepared` >>
  drule_all abi_decode_dynamic_element_setup_counters >> strip_tac >>
  `st.cs_next_var <= ready.cs_next_var` by
    (Cases_on `hi = Lit 0w` >> asm_simp_tac arith_ss []) >>
  `abi_decoder_operand_live ready.cs_next_var hi` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> asm_simp_tac bool_ss []) >>
  drule_all abi_decoder_address_frame_ranges >> strip_tac >>
  drule_all abi_decoder_address_frame_source >> disch_then (qspec_then `opc` assume_tac) >>
  RULE_ASSUM_TAC (SIMP_RULE bool_ss [GSYM ADD_ASSOC]) >>
  mp_tac (SIMP_RULE bool_ss [LET_THM, GSYM ADD_ASSOC]
    (Q.INST [`s` |-> `prepared:venom_state`, `st` |-> `ready`,
      `childsrc` |-> `FST (SND (ops:operand # operand # operand))`,
      `childdst` |-> `SND (SND (ops:operand # operand # operand))`]
      abi_decoder_valid_array_child_pre)) >>
  impl_tac >- asm_simp_tac bool_ss [GSYM ADD_ASSOC] >> strip_tac >>
  qexists_tac `prepared` >>
  asm_simp_tac bool_ss [abi_decoder_valid_array_entry_def, LET_THM, GSYM ADD_ASSOC]
QED

Theorem abi_decoder_valid_array_setup_from_state:
  abi_decode_array_element_setup ip src dst opc hi (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) st = (ops,ready) /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) di
    (dec (Array NONE (vyper_to_abi_type env ty)) bs) (ArrayV (DynArrayV vs)) /\
  vyper_decode_valid_enc (Array NONE (vyper_to_abi_type env ty)) bs /\ j < LENGTH vs /\
  is_dynamic (vyper_to_abi_type env ty) /\
  (!elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) /\
  abi_decoder_ranges opc hi src dst sb (LENGTH bs)
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source opc initial) = bs /\
  eval_operand ip initial = SOME p /\ mload (w2n p) initial = n2w j /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  ready.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  frag_exec ctx st ready (\s. s = initial)
    (abi_decoder_valid_array_entry ce env sf ty tv bs vs j ready ops opc hi sb d b cap
      st.cs_next_var limit_st initial) (K F)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode opc` by fs[abi_decoder_ranges_def] >>
  drule_all abi_decode_array_element_setup_shape >> strip_tac >>
  irule frag_exec_run_inst_seq >> simp[] >>
  drule_all abi_decoder_valid_array_setup_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st ready) initial = OK prepared` >>
  qexists_tac `prepared` >> asm_simp_tac bool_ss []
QED

Theorem abi_decoder_valid_array_setup_reach:
  abi_decode_array_element_setup ip src dst opc hi (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) st = (ops,ready) /\
  fn_has_code st ready func /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) di
    (dec (Array NONE (vyper_to_abi_type env ty)) bs) (ArrayV (DynArrayV vs)) /\
  vyper_decode_valid_enc (Array NONE (vyper_to_abi_type env ty)) bs /\ j < LENGTH vs /\
  is_dynamic (vyper_to_abi_type env ty) /\
  (!elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) /\
  abi_decoder_ranges opc hi src dst sb (LENGTH bs)
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source opc initial) = bs /\
  eval_operand ip initial = SOME p /\ mload (w2n p) initial = n2w j /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  ready.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?prepared. abi_decoder_valid_array_entry ce env sf ty tv bs vs j ready ops opc hi sb d b cap
      st.cs_next_var limit_st initial prepared /\
    prepared.vs_current_bb = ready.cs_current_bb /\
    prepared.vs_inst_idx = LENGTH ready.cs_current_insts /\ ~prepared.vs_halted /\
    abi_decode_sim ctx func initial prepared
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_valid_array_setup_from_state >> disch_then (qspec_then `ctx` assume_tac) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial prepared` >>
  `~prepared.vs_halted` by fs[abi_decoder_valid_array_entry_def, abi_decoder_address_frame_def] >>
  qexists_tac `prepared` >> asm_simp_tac bool_ss []
QED
