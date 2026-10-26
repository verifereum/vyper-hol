(* Actual array setup followed by the recursive child correctness hypothesis. *)
Theory abiDecoderArrayBody
Ancestors
  abiDecoderArrayEntry abiDecoderArraySetupInputs abiDecoderArraySlice
  abiDecoderCorrect abiDecoderEffect abiDecoderCounters abiDecoderAppend
  abiDecoderCoherence abiDecoderTypedContract abiDecoderReentry
  abiDecoderDynamicLoopSetup abiDecoderAllocation abiDecoderArrayInitExec
  abiDecoderReservation abiDecoderLoop abiDecoderContract fragExec
  abiDecoderLoopSetup abiEncoder compileEnv valueEncoding vyperABI vyperValue
  venomState venomExecSemantics emitHelperProps words list arithmetic

Theorem abi_decoder_array_body_code:
  abi_decode_array_element_setup ip src dst opc hi info asz msz st = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) opc hi info middle = ((),end_st) /\
  abi_decode_source_opcode opc /\ fn_has_code st end_st func ==>
  fn_has_code st middle func /\ fn_has_code middle end_st func /\
  st.cs_next_var <= middle.cs_next_var /\ middle.cs_next_var <= end_st.cs_next_var /\
  abi_decoder_operand_live middle.cs_next_var (FST ops)
Proof
  strip_tac >> drule_all abi_decode_array_element_setup_shape >> strip_tac >>
  `cs_extends st middle` by (irule cs_extends_same_block >> simp[]) >>
  drule cs_extends_abi_decode >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  drule abi_decode_array_element_setup_operands >> strip_tac >>
  drule abi_decoder_variable_counter >> strip_tac >> asm_simp_tac bool_ss []
QED

Theorem abi_decoder_budget_child_reservation:
  abi_decoder_budget first last b cap s /\ first <= child_id ==>
  abi_decoder_reservation child_id last b cap s
Proof
  strip_tac >> drule abi_decoder_budget_reservation >> strip_tac >>
  mp_tac (Q.INST [`next` |-> `child_id:num`, `t` |-> `s:venom_state`]
    abi_decoder_reservation_advance) >> asm_simp_tac bool_ss []
QED

Theorem abi_decoder_address_then_effect:
  abi_decoder_address_frame next s prepared /\ fresh_vars_wrt limit_st prepared /\
  abi_decoder_budget first last b cap s /\
  abi_decoder_effect first last child_lo hi child_next limit_st d sz b cap prepared t /\
  lo <= child_lo /\ next <= child_next ==>
  abi_decoder_effect first last lo hi next limit_st d sz b cap s t
Proof
  strip_tac >>
  `abi_decoder_effect first last lo hi next limit_st d sz b cap s prepared` by
    (irule abi_decoder_address_effect >> asm_simp_tac bool_ss [] >>
     qexists_tac `next` >> simp[]) >>
  `abi_decoder_effect first last lo hi next limit_st d sz b cap prepared t` by
    (drule_all (SIMP_RULE (srw_ss()) []
      (Q.INST [`child_hi` |-> `hi:num`, `child_d` |-> `d:num`, `child_sz` |-> `sz:num`]
        abi_decoder_effect_widen)) >> simp[]) >>
  drule_all abi_decoder_effect_trans >> simp[]
QED

Theorem abi_decoder_array_body:
  abi_decode_array_element_setup ip src dst opc hi (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) st = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) opc hi
    (type_to_abi_dec_info sf ce ty) middle = ((),end_st) /\
  fn_has_code st end_st func /\
  (!bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_correct ce env sf ty tv /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV (pre ++ av::post)) (ArrayV (DynArrayV (vpre ++ v::vpost))) /\
  LENGTH pre = LENGTH vpre /\
  abi_decoder_ranges opc hi src dst sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV (pre ++ av::post))))
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty))
    (ListV (pre ++ av::post)))) (abi_decode_source opc initial) =
    enc (Array NONE (vyper_to_abi_type env ty)) (ListV (pre ++ av::post)) /\
  eval_operand ip initial = SOME p /\ mload (w2n p) initial = n2w (LENGTH pre) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\ abi_decoder_operand_live st.cs_next_var ip /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\
  st.cs_next_id <= middle.cs_next_id /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. val_in_memory tv v (d + 32 + LENGTH pre * type_memory_bytes ce ty) actual.vs_memory /\
    abi_decoder_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var limit_st
      (d + 32 + LENGTH pre * type_memory_bytes ce ty) (type_memory_bytes ce ty) b cap initial actual /\
    eval_operand (FST ops) actual = SOME (n2w (LENGTH pre)) /\ eval_operand ip actual = SOME p /\
    actual.vs_current_bb = end_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode opc` by fs[abi_decoder_ranges_def, Excl "enc_def"] >>
  drule_all abi_decoder_array_body_code >> strip_tac >>
  `first <= middle.cs_next_id /\ middle.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  `abi_decoder_reservation middle.cs_next_id last b cap initial` by
    (drule_all abi_decoder_budget_child_reservation >> simp[]) >>
  drule_all abi_decoder_array_setup_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qpat_assum `abi_decoder_array_entry ce env sf ty tv av v middle last ops opc hi
      child_sb child_d b cap next limit_st initial i prepared`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_array_entry_def]) >>
  qpat_assum `abi_decoder_address_frame _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
  `abi_decoder_budget first last b cap prepared` by
    (drule_all abi_decoder_budget_transport >> simp[]) >>
  drule_all abi_decoder_correct_run_simple >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `val_in_memory tv v (d + 32 + LENGTH pre * type_memory_bytes ce ty) actual.vs_memory` >>
  `abi_decoder_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var limit_st
      (d + 32 + LENGTH pre * type_memory_bytes ce ty) (type_memory_bytes ce ty) b cap initial actual` by
    (mp_tac (Q.INST [`lo` |-> `st.cs_next_id`, `hi` |-> `end_st.cs_next_id`,
      `next` |-> `st.cs_next_var`, `child_lo` |-> `middle.cs_next_id`,
      `child_next` |-> `middle.cs_next_var`, `s` |-> `initial:venom_state`,
      `prepared` |-> `prepared:venom_state`, `t` |-> `actual:venom_state`,
      `d` |-> `d + 32 + LENGTH (pre:abi_value list) * type_memory_bytes ce ty`,
      `sz` |-> `type_memory_bytes ce ty`] abi_decoder_address_then_effect) >>
     asm_simp_tac bool_ss []) >>
  `eval_operand (FST ops) actual = SOME (n2w (LENGTH pre)) /\ eval_operand ip actual = SOME p`
    by (fs[abi_decoder_effect_def, Excl "enc_def"] >> metis_tac[]) >>
  `abi_decode_sim ctx func initial actual` by metis_tac[abi_decode_sim_trans] >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED
