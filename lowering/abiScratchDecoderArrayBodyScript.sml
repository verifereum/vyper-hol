(* Execute an actual array child under the physical recursive contract. *)
Theory abiScratchDecoderArrayBody
Ancestors
  abiScratchDecoderContract abiScratchDecoderArrayEntry abiScratchEncoderContract
  abiScratchAfterAddress abiScratchEffect abiDecoderArrayBody abiDecoderArraySetupInputs
  abiDecoderArrayInitExec abiDecoderDynamicLoopSetup abiDecoderCoherence abiDecoderTypedContract
  abiDecoderContract abiDecoderReentry abiDecoderLoop abiDecodeRanges abiValidMember
  abiValidMembers abiEncoder fragExec compileEnv valueEncoding vyperABI vyperValue contractABI
  venomState venomExecSemantics words list arithmetic

Theorem abi_scratch_decoder_array_body:
  abi_decode_array_element_setup ip src dst opc hi (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) st = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) opc hi
    (type_to_abi_dec_info sf ce ty) middle = ((),end_st) /\
  fn_has_code st end_st func /\
  (!bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  abi_scratch_decoder ce env sf ty tv /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    di (dec (Array NONE (vyper_to_abi_type env ty)) bs) (ArrayV (DynArrayV vs)) /\
  vyper_decode_valid_enc (Array NONE (vyper_to_abi_type env ty)) bs /\ j < LENGTH vs /\
  (is_dynamic (vyper_to_abi_type env ty) ==>
    !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) /\
  abi_scratch_decoder_ranges opc hi src dst sb (LENGTH bs)
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) first last b cap initial /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source opc initial) = bs /\
  eval_operand ip initial = SOME p /\ mload (w2n p) initial = n2w j /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\ abi_decoder_operand_live st.cs_next_var ip /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\
  st.cs_next_id <= middle.cs_next_id /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. val_in_memory tv (EL j vs) (d + 32 + j * type_memory_bytes ce ty) actual.vs_memory /\
    abi_scratch_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var limit_st
      (d + 32 + j * type_memory_bytes ce ty) (type_memory_bytes ce ty) b cap initial actual /\
    eval_operand (FST ops) actual = SOME (n2w j) /\ eval_operand ip actual = SOME p /\
    actual.vs_current_bb = end_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode opc` by fs[abi_scratch_decoder_ranges_def] >>
  drule_all abi_decoder_array_body_code >> strip_tac >>
  `first <= middle.cs_next_id /\ middle.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all abi_scratch_decoder_array_setup_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial prepared` >>
  `abi_decoder_budget first last b cap prepared` by
    (qpat_assum `abi_decoder_address_frame _ _ _`
      (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
     drule_all abi_decoder_budget_transport >> simp[]) >>
  qhdtm_x_assum `abi_scratch_decoder` (mp_tac o PURE_REWRITE_RULE [abi_scratch_decoder_def]) >>
  disch_then (qspecl_then [`SND (SND (ops:operand # operand # operand))`,
    `FST (SND (ops:operand # operand # operand))`, `opc`, `hi`, `middle`, `end_st`,
    `func`, `ctx`, `first`, `last`, `b`, `cap`, `limit_st`, `prepared:venom_state`,
    `abi_decode_member_bytes (vyper_to_abi_type env ty) (DROP 32 bs)
      (DROP (j * abi_member_head_size (vyper_to_abi_type env ty)) (DROP 32 bs))`,
    `EL j (vs:vyperValue$value list)`,
    `sb + (32 + abi_decode_member_offset (vyper_to_abi_type env ty) (DROP 32 bs)
      (j * abi_member_head_size (vyper_to_abi_type env ty)))`,
    `d + 32 + j * type_memory_bytes ce ty`] mp_tac) >>
  impl_tac >- asm_simp_tac bool_ss [] >>
  disch_then (qx_choose_then `actual` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  `eval_operand (FST ops) actual = SOME (n2w j)` by
    (drule_all abi_scratch_effect_operand >> simp[]) >>
  `abi_scratch_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var limit_st
      (d + 32 + j * type_memory_bytes ce ty) (type_memory_bytes ce ty) b cap initial actual` by
    (irule abi_scratch_effect_after_address >>
     qexistsl_tac [`d + 32 + j * type_memory_bytes ce ty`, `end_st.cs_next_id`,
       `middle.cs_next_id`, `middle.cs_next_var`, `type_memory_bytes ce ty`, `prepared`] >>
     asm_simp_tac arith_ss []) >>
  `eval_operand ip actual = SOME p` by (drule_all abi_scratch_effect_operand >> simp[]) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  irule abi_decode_sim_trans >> qexists_tac `prepared` >> asm_simp_tac bool_ss []
QED
