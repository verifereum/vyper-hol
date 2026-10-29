(* Execute the existing tuple-slot action, including its mandatory ADD at zero. *)
Theory abiTupleEncodeSlot
Ancestors
  abiTupleProps abiTupleEncodeInput abiTupleEncodeWrite abiBuiltinPrefix
  abiDecoderReentry abiDecoderReentryAddress abiDecoderDynamicLoopSetup abiDecoderContract abiDecoderGuards
  abiDecoderFrameCompose compileEnv context emitHelper emitHelperProps exprLoweringProps
  venomState venomExecSemantics venomInst words list rich_list arithmetic

Theorem abi_tuple_encode_slot_shape:
  compile_abi_tuple_slot ce buf off op ty st = ((),final) ==>
  final.cs_next_var = st.cs_next_var+1 /\ st.cs_next_id < final.cs_next_id /\
  final.cs_blocks = st.cs_blocks /\ final.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts final.cs_current_insts /\ inst_extends st final /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts st final)
Proof
  Cases_on `is_word_type ty` >> Cases_on `type_memory_bytes ce ty` >>
  asm_simp_tac (srw_ss()) [compile_abi_tuple_slot_def, compile_copy_memory_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def, emit_void_def,
    fresh_var_def, fresh_id_def, emit_def] >> rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[inst_extends_def, emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, IS_PREFIX_APPEND, is_terminator_def, mk_inst_def]
QED

Theorem abi_tuple_encode_slot_sequence:
  compile_abi_tuple_slot ce buf off op ty st = ((),final) /\
  eval_operand buf s = SOME (n2w baddr) /\ baddr+off < dimword (:256) /\ lo <= hi /\
  abi_tuple_encode_input sf ce ty at av op st.cs_next_var lo hi s /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?actual. run_inst_seq (emitted_insts st final) s = OK actual /\ inst_extends st final /\
    abi_encoder_input (type_to_abi_enc_info sf ce ty) at av (baddr+off)
      (type_memory_bytes ce ty) actual.vs_memory /\
    fresh_vars_wrt limit_st actual /\ abi_decode_frame (baddr+off) (type_memory_bytes ce ty) s actual /\
    actual.vs_allocas = s.vs_allocas /\ actual.vs_alloca_next = s.vs_alloca_next /\
    actual.vs_halted = s.vs_halted /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op actual = SOME w)
Proof
  strip_tac >> drule abi_tuple_encode_slot_shape >> strip_tac >>
  qpat_x_assum `compile_abi_tuple_slot _ _ _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [compile_abi_tuple_slot_def, comp_bind_def, LET_THM] >> pairarg_tac >> strip_tac >>
  rename1 `emit_op ADD [buf;Lit (n2w off)] st = (dst,address_st)` >>
  qpat_assum `emit_op ADD [buf;Lit (n2w off)] st = (dst,address_st)` (fn eq =>
    qpat_x_assum `(\(dst,cs'). _) _ = _` (assume_tac o SIMP_RULE (srw_ss()) [eq])) >>
  drule emitted_insts_emit_op >> strip_tac >>
  `address_st.cs_next_var <= limit_st.cs_next_var /\ st.cs_next_var <= address_st.cs_next_var` by decide_tac >>
  mp_tac (Q.INST [`lhs` |-> `buf`, `rhs` |-> `Lit (n2w off)`, `out` |-> `dst`,
    `a` |-> `n2w baddr:bytes32`, `b` |-> `n2w off:bytes32`, `st'` |-> `address_st`] abi_builtin_emit_add) >>
  impl_tac >- asm_simp_tac (srw_ss()) [eval_operand_def] >> strip_tac >>
  rename1 `abi_builtin_prefix st address_st limit_st s addressed` >>
  qpat_assum `abi_builtin_prefix _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_prefix_def]) >>
  qpat_assum `abi_decoder_address_frame _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
  `eval_operand dst addressed = SOME (n2w (baddr+off))` by fs[word_add_n2w] >>
  `abi_tuple_encode_input sf ce ty at av op address_st.cs_next_var lo hi addressed` by
    (mp_tac (Q.INST [`next` |-> `st.cs_next_var`, `later` |-> `address_st.cs_next_var`,
       `t` |-> `addressed:venom_state`] abi_tuple_encode_input_transport) >>
     impl_tac >- asm_simp_tac bool_ss [abi_decode_frame_def] >> simp[]) >>
  drule_all abi_tuple_encode_write >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts address_st final) addressed = OK actual` >>
  `run_inst_seq (emitted_insts st final) s = OK actual /\ inst_extends st final` by
    (mp_tac (Q.INST [`st1` |-> `address_st`, `st2` |-> `final`,
      `s1` |-> `addressed:venom_state`, `s2` |-> `actual:venom_state`] abi_decode_sequence_chain) >>
     asm_simp_tac bool_ss []) >>
  `abi_decode_frame (baddr+off) (type_memory_bytes ce ty) s actual` by
    (irule abi_decode_frame_trans >> qexists_tac `addressed` >> asm_simp_tac bool_ss [abi_decode_frame_def]) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  rpt strip_tac >> first_x_assum irule >> asm_simp_tac bool_ss []
QED
