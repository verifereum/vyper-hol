Theory abiTupleEncodeZeroSlot
Ancestors
  valueEncodingDefs
  abiTupleEncodeOpenSlot abiTupleEncodeZeroInput abiTupleEncodeOpenResult
  abiTupleEncodeOpenMemory abiTupleEncodeSlot abiTupleEncodeInput abiEncoderOpenInput abiEncoderOpenRelocate
  abiBuiltinEncodeCorrect abiBuiltinEncodeWord abiEncoderWrites abiEncoderBytes
  abiEncoderInputFrame abiDecoderReentry abiDecoderContract abiDecoderGuards abiDecoderRange
  abiDecoderFrameCompose compileEnv context emitHelper emitHelperProps exprLoweringProps
  valueEncoding valueEncodingProps venomState venomExecSemantics words list arithmetic
  abiTupleProps abiBuiltinPrefix abiDecoderReentryAddress abiDecoderDynamicLoopSetup venomInst rich_list

Theorem abi_tuple_encode_zero_word_write:
  is_word_type ty /\ emit_void MSTORE [dst;op] st = ((),final) /\
  eval_operand dst s = SOME (n2w d) /\ d < dimword (:256) /\ fresh_vars_wrt limit_st s /\
  abi_tuple_encode_zero_input sf ce ty at av op next lo hi s ==>
  ?actual. run_inst_seq (emitted_insts st final) s = OK actual /\ inst_extends st final /\
    abi_encoder_open_input (type_to_abi_enc_info sf ce ty) at av d (type_memory_bytes ce ty) actual.vs_memory /\
    fresh_vars_wrt limit_st actual /\ abi_decode_frame d (type_memory_bytes ce ty) s actual /\
    actual.vs_allocas = s.vs_allocas /\ actual.vs_alloca_next = s.vs_alloca_next /\
    actual.vs_halted = s.vs_halted /\ (!op. eval_operand op actual = eval_operand op s)
Proof
  strip_tac >>
  `abi_tuple_encode_input sf ce ty at av op next lo hi s` by
    gvs[abi_tuple_encode_input_def, abi_tuple_encode_zero_input_def] >>
  drule_all abi_tuple_encode_word_write >> strip_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  irule abi_encoder_input_open >> asm_simp_tac bool_ss []
QED

Theorem abi_tuple_encode_zero_copy_write:
  ~is_word_type ty /\ compile_copy_memory dst op (type_memory_bytes ce ty) st = ((),final) /\
  eval_operand dst s = SOME (n2w d) /\ d < dimword (:256) /\ fresh_vars_wrt limit_st s /\
  abi_tuple_encode_zero_input sf ce ty at av op next lo hi s ==>
  ?actual. run_inst_seq (emitted_insts st final) s = OK actual /\ inst_extends st final /\
    abi_encoder_open_input (type_to_abi_enc_info sf ce ty) at av d (type_memory_bytes ce ty) actual.vs_memory /\
    fresh_vars_wrt limit_st actual /\ abi_decode_frame d (type_memory_bytes ce ty) s actual /\
    actual.vs_allocas = s.vs_allocas /\ actual.vs_alloca_next = s.vs_alloca_next /\
    actual.vs_halted = s.vs_halted /\ (!op. eval_operand op actual = eval_operand op s)
Proof
  strip_tac >> qpat_x_assum `abi_tuple_encode_zero_input _ _ _ _ _ _ _ _ _ _` mp_tac >>
  asm_simp_tac bool_ss [abi_tuple_encode_zero_input_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `?sb source_cap. eval_operand op s = SOME (n2w sb) /\ _`
    (qx_choose_then `sb` (qx_choose_then `source_cap`
      (MAP_EVERY assume_tac o CONJUNCTS))) >>
  Cases_on `type_memory_bytes ce ty = 0`
  >- (gvs[compile_copy_memory_def, comp_return_def] >>
      `abi_encoder_open_input (type_to_abi_enc_info sf ce ty) at av d 0 s.vs_memory` by
        (irule abi_encoder_open_input_relocate_capacity >>
         goal_assum (drule_at Any) >> simp[mem_bytes_at_def]) >>
      qexists_tac `s` >> simp[emitted_insts_def, run_inst_seq_def, inst_extends_def, abi_decode_frame_def]) >>
  `emit_void MCOPY [dst;op;Lit (n2w (type_memory_bytes ce ty))] st = ((),final)` by
    (Cases_on `type_memory_bytes ce ty` >> gvs[compile_copy_memory_def]) >>
  mp_tac (Q.INST [`src` |-> `op`, `dst` |-> `dst`,
    `len` |-> `Lit (n2w (type_memory_bytes ce ty))`, `cnt` |-> `type_memory_bytes ce ty`,
    `db` |-> `d`, `st'` |-> `final`] abi_encoder_emit_copy) >>
  impl_tac >- asm_simp_tac (srw_ss()) [eval_operand_def] >> strip_tac >>
  `abi_decode_frame d (type_memory_bytes ce ty) s (mcopy d sb (type_memory_bytes ce ty) s)` by
    (simp_tac bool_ss [abi_decode_frame_def] >> conj_tac
     >- (rpt strip_tac >> irule mcopy_mem_bytes_at_disjoint >> asm_simp_tac bool_ss []) >> simp[]) >>
  `abi_encoder_open_input (type_to_abi_enc_info sf ce ty) at av d (type_memory_bytes ce ty)
    (mcopy d sb (type_memory_bytes ce ty) s).vs_memory` by
    (irule abi_encoder_open_input_mcopy_prefix >> goal_assum (drule_at Any) >> asm_rewrite_tac[]) >>
  qexists_tac `mcopy d sb (type_memory_bytes ce ty) s` >>
  asm_simp_tac (srw_ss()) [abi_encoder_copy_eval]
QED

Theorem abi_tuple_encode_zero_write:
  (if is_word_type ty then emit_void MSTORE [dst;op]
   else compile_copy_memory dst op (type_memory_bytes ce ty)) st = ((),final) /\
  eval_operand dst s = SOME (n2w d) /\ d < dimword (:256) /\ fresh_vars_wrt limit_st s /\
  abi_tuple_encode_zero_input sf ce ty at av op next lo hi s ==>
  ?actual. run_inst_seq (emitted_insts st final) s = OK actual /\ inst_extends st final /\
    abi_encoder_open_input (type_to_abi_enc_info sf ce ty) at av d (type_memory_bytes ce ty) actual.vs_memory /\
    fresh_vars_wrt limit_st actual /\ abi_decode_frame d (type_memory_bytes ce ty) s actual /\
    actual.vs_allocas = s.vs_allocas /\ actual.vs_alloca_next = s.vs_alloca_next /\
    actual.vs_halted = s.vs_halted /\ (!op. eval_operand op actual = eval_operand op s)
Proof
  Cases_on `is_word_type ty` >> asm_simp_tac bool_ss [] >> strip_tac
  >- (drule_all abi_tuple_encode_zero_word_write >> simp[]) >>
  drule_all abi_tuple_encode_zero_copy_write >> simp[]
QED

Theorem abi_tuple_encode_zero_slot_sequence:
  compile_abi_tuple_slot ce buf off op ty st = ((),final) /\
  eval_operand buf s = SOME (n2w baddr) /\ baddr+off < dimword (:256) /\ lo <= hi /\
  abi_tuple_encode_zero_input sf ce ty at av op st.cs_next_var lo hi s /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?actual. run_inst_seq (emitted_insts st final) s = OK actual /\ inst_extends st final /\
    abi_encoder_open_input (type_to_abi_enc_info sf ce ty) at av (baddr+off)
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
  `abi_tuple_encode_zero_input sf ce ty at av op address_st.cs_next_var lo hi addressed` by
    (irule abi_tuple_encode_zero_input_transport >> conj_tac >- asm_simp_tac bool_ss [] >>
     qexistsl_tac [`st.cs_next_var`, `s`] >>
     asm_simp_tac bool_ss [abi_decode_frame_def]) >>
  drule_all abi_tuple_encode_zero_write >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts address_st final) addressed = OK actual` >>
  `run_inst_seq (emitted_insts st final) s = OK actual /\ inst_extends st final` by
    (irule abi_decode_sequence_chain >> goal_assum (drule_at Any) >>
     asm_simp_tac bool_ss [] >> qexists_tac `addressed` >> asm_simp_tac bool_ss []) >>
  `abi_decode_frame (baddr+off) (type_memory_bytes ce ty) s actual` by
    (irule abi_decode_frame_trans >> qexists_tac `addressed` >> asm_simp_tac bool_ss [abi_decode_frame_def]) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  rpt strip_tac >> first_x_assum irule >> asm_simp_tac bool_ss []
QED

Theorem abi_tuple_encode_zero_result_slot:
  compile_abi_tuple_slot ce buf off op ty st = ((),final) /\
  eval_operand buf s = SOME (n2w baddr) /\ baddr+off < dimword (:256) /\ lo <= hi /\
  abi_tuple_encode_zero_input sf ce ty at av op st.cs_next_var lo hi s /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?actual. abi_tuple_encode_open_result sf ce [(op,ty)] [at] [av] st final limit_st (baddr+off) s actual
Proof
  strip_tac >> drule_all abi_tuple_encode_zero_slot_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st final) s = OK actual` >> qexists_tac `actual` >>
  asm_simp_tac (srw_ss()) [abi_tuple_encode_open_result_def, abi_tuple_encode_open_memory_def, abi_tuple_bytes_def]
QED
