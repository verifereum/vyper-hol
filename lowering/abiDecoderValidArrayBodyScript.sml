(* Actual dynamic-array address setup followed by source-valid child execution. *)
Theory abiDecoderValidArrayBody
Ancestors
  abiDecoderValidContract abiDecoderValidArrayEntry abiDecoderArrayBody
  abiDecoderArraySetupInputs abiDecoderCoherence abiDecoderTypedContract abiDecoderEffect
  abiDecoderReentry abiDecoderDynamic abiDecoderDynamicLoopSetup abiDecoderAllocation
  abiDecoderArrayInitExec abiDecoderLoop abiDecoderContract abiDecodeRanges abiValidMember
  abiValidMembers abiEncoder fragExec compileEnv valueEncoding vyperABI vyperValue contractABI
  venomState venomExecSemantics words list arithmetic

Theorem abi_decoder_valid_array_body:
  abi_decode_array_element_setup ip src dst opc hi (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) st = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) opc hi
    (type_to_abi_dec_info sf ce ty) middle = ((),end_st) /\
  fn_has_code st end_st func /\
  (!bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_valid_correct ce env sf ty tv /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    di (dec (Array NONE (vyper_to_abi_type env ty)) bs) (ArrayV (DynArrayV vs)) /\
  valid_enc (Array NONE (vyper_to_abi_type env ty)) bs /\ j < LENGTH vs /\
  is_dynamic (vyper_to_abi_type env ty) /\
  (!elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) /\
  abi_decoder_ranges opc hi src dst sb
    (LENGTH bs)
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source opc initial) =
    bs /\
  eval_operand ip initial = SOME p /\ mload (w2n p) initial = n2w j /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\ abi_decoder_operand_live st.cs_next_var ip /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\
  st.cs_next_id <= middle.cs_next_id /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. val_in_memory tv (EL j vs) (d + 32 + j * type_memory_bytes ce ty) actual.vs_memory /\
    abi_decoder_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var limit_st
      (d + 32 + j * type_memory_bytes ce ty) (type_memory_bytes ce ty) b cap initial actual /\
    eval_operand (FST ops) actual = SOME (n2w j) /\ eval_operand ip actual = SOME p /\
    actual.vs_current_bb = end_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode opc` by fs[abi_decoder_ranges_def, Excl "enc_def"] >>
  drule_all abi_decoder_array_body_code >> strip_tac >>
  `first <= middle.cs_next_id /\ middle.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all abi_decoder_valid_array_setup_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qpat_assum `abi_decoder_valid_array_entry ce env sf ty tv bs vs j middle ops opc hi sb d b cap
      st.cs_next_var limit_st initial prepared`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE bool_ss [abi_decoder_valid_array_entry_def, LET_THM]) >>
  qpat_assum `abi_decoder_address_frame _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
  `abi_decoder_budget first last b cap prepared` by
    (drule_all abi_decoder_budget_transport >> simp[]) >>
  mp_tac (Q.INST [`start` |-> `middle`, `end_st` |-> `end_st`,
    `initial` |-> `prepared:venom_state`, `dst` |-> `SND (SND (ops:operand # operand # operand))`,
    `src` |-> `FST (SND (ops:operand # operand # operand))`,
    `bs` |-> `abi_decode_member_bytes (vyper_to_abi_type env ty) (DROP 32 bs)
      (DROP (j * abi_member_head_size (vyper_to_abi_type env ty)) (DROP 32 bs))`,
    `v` |-> `EL j (vs:vyperValue$value list)`,
    `sb` |-> `sb + (32 + abi_decode_member_offset (vyper_to_abi_type env ty) (DROP 32 bs)
      (j * abi_member_head_size (vyper_to_abi_type env ty)))`,
    `d` |-> `d + 32 + j * type_memory_bytes ce ty`] abi_decoder_valid_correct_run) >>
  impl_tac >- asm_simp_tac bool_ss [] >>
  disch_then (qx_choose_then `actual` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  `abi_decoder_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var limit_st
      (d + 32 + j * type_memory_bytes ce ty) (type_memory_bytes ce ty) b cap initial actual` by
    (mp_tac (Q.INST [`lo` |-> `st.cs_next_id`, `hi` |-> `end_st.cs_next_id`,
      `next` |-> `st.cs_next_var`, `child_lo` |-> `middle.cs_next_id`,
      `child_next` |-> `middle.cs_next_var`, `s` |-> `initial:venom_state`,
      `prepared` |-> `prepared:venom_state`, `t` |-> `actual:venom_state`,
      `d` |-> `d + 32 + j * type_memory_bytes ce ty`,
      `sz` |-> `type_memory_bytes ce ty`] abi_decoder_address_then_effect) >>
     asm_simp_tac bool_ss []) >>
  `eval_operand (FST ops) actual = SOME (n2w j) /\ eval_operand ip actual = SOME p`
    by (fs[abi_decoder_effect_def, Excl "enc_def"] >> metis_tac[]) >>
  `abi_decode_sim ctx func initial actual` by metis_tac[abi_decode_sim_trans] >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED
