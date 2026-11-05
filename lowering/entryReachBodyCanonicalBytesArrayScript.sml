(* Actual-state bridges for canonical arrays with bytestring elements. *)
Theory entryReachBodyCanonicalBytesArray
Ancestors
  entryReachBodyCanonicalBytes entryReachBodyCanonicalChildAddress
  entryReachBodyExactArrayLoop entryReachBodyArrayInit calldataBytesLeaf
  abiEncoderSequence abiDecoderReentryPointer ctorAbiActualBytes
  abiDecoderTypedContract abiDecoderCoherence abiDecoderFrame abiDecoderDynamicLoopSetup
  abiDecoderArraySetupInputs abiDecoderReentry
  abiDecoderBytesTyped abiDecoderContract abiEncoder emitHelper emitHelperProps exprLoweringProps compileEnv rich_list
  venomExecSemantics venomExecProofs venomState venomInst valueEncoding words list arithmetic finite_map

Theorem entry_bytes_step_fields[local]:
  MEM i.inst_opcode [CALLDATALOAD; GT; ISZERO; ASSERT; CALLDATACOPY] /\
  step_inst_base i s = OK t ==> entry_loop_fields s t
Proof
  simp_tac bool_ss [MEM] >> strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  pure_rewrite_tac[step_inst_base_def] >>
  pure_asm_rewrite_tac[opcode_case_def] >>
  simp[exec_read1_def, exec_pure2_def, exec_pure1_def,
       AllCaseEqs()] >> strip_tac >>
  gvs[entry_loop_fields_def, update_var_def, write_memory_with_expansion_def]
QED

Theorem entry_bytes_sequence_fields[local]:
  !code s t.
  EVERY (\i. MEM i.inst_opcode [CALLDATALOAD; GT; ISZERO; ASSERT; CALLDATACOPY]) code /\
  run_inst_seq code s = OK t ==> entry_loop_fields s t
Proof
  Induct >- simp[run_inst_seq_def, entry_loop_fields_def] >> rpt gen_tac >>
  simp_tac (srw_ss()) [run_inst_seq_def, EVERY_DEF, AllCaseEqs(), Excl "MEM"] >> strip_tac >>
  `MEM h.inst_opcode [CALLDATALOAD; GT; ISZERO; ASSERT; CALLDATACOPY]` by simp[] >>
  drule_all entry_bytes_step_fields >> strip_tac >>
  rename1 `run_inst_seq code middle = OK t` >>
  first_x_assum (qspecl_then [`middle`,`t`] mp_tac) >>
  gvs[MEM, entry_loop_fields_def]
QED

Theorem entry_bytes_code_fields[local]:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (DecBytestring n) st = ((),st') /\
  run_inst_seq (emitted_insts st st') s = OK t ==> entry_loop_fields s t
Proof
  strip_tac >>
  `EVERY (\i. MEM i.inst_opcode [CALLDATALOAD; GT; ISZERO; ASSERT; CALLDATACOPY])
    (emitted_insts st st')` by
    (qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` mp_tac >>
     simp[compile_abi_decode_to_buf_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def] >> rpt strip_tac >> gvs[emitted_insts_def] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
     simp[DROP_LENGTH_APPEND, mk_inst_def]) >>
  drule_all entry_bytes_sequence_fields >> simp[]
QED

Theorem entry_canonical_bytes_observed[local]:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (DecBytestring n) st = ((),st') /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  LENGTH bs <= n /\ n < dimword (:256) /\
  sb + LENGTH (enc (Bytes NONE) (contractABI$BytesV bs)) < dimword (:256) /\
  d + abi_decode_bytes_copy_size n < dimword (:256) /\
  mem_bytes_at sb (LENGTH (enc (Bytes NONE) (contractABI$BytesV bs)))
    s.vs_call_ctx.cc_calldata = enc (Bytes NONE) (contractABI$BytesV bs) ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    val_in_memory (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV bs) d t.vs_memory /\
    abi_decode_frame d (abi_decode_bytes_copy_size n) s t /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    entry_loop_fields s t
Proof
  strip_tac >> drule_all entry_canonical_bytes_sequence >> strip_tac >>
  drule_all entry_bytes_code_fields >> strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem entry_bytes_step_var[local]:
  MEM i.inst_opcode [CALLDATALOAD; GT; ISZERO; ASSERT; CALLDATACOPY] /\
  step_inst_base i s = OK t /\ ~MEM x i.inst_outputs ==>
  FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x
Proof
  simp_tac bool_ss [MEM] >> strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  pure_rewrite_tac[step_inst_base_def] >>
  pure_asm_rewrite_tac[opcode_case_def] >>
  simp[exec_read1_def, exec_pure2_def, exec_pure1_def,
       AllCaseEqs()] >> strip_tac >>
  gvs[update_var_def, write_memory_with_expansion_def, MEM,
      finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem entry_bytes_sequence_var[local]:
  !code s t x.
  EVERY (\i. MEM i.inst_opcode [CALLDATALOAD; GT; ISZERO; ASSERT; CALLDATACOPY] /\
    ~MEM x i.inst_outputs) code /\ run_inst_seq code s = OK t ==>
  FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x
Proof
  Induct >- simp[run_inst_seq_def] >> rpt gen_tac >>
  simp_tac (srw_ss()) [run_inst_seq_def, EVERY_DEF, AllCaseEqs(), Excl "MEM"] >> strip_tac >>
  `MEM h.inst_opcode [CALLDATALOAD; GT; ISZERO; ASSERT; CALLDATACOPY]` by simp[] >>
  drule_all entry_bytes_step_var >> strip_tac >>
  rename1 `run_inst_seq code middle = OK t` >>
  first_x_assum (qspecl_then [`middle`,`t`,`x`] mp_tac) >> simp[]
QED

Theorem entry_bytes_outputs[local]:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (DecBytestring n) st = ((),st') ==>
  EVERY (\i. MEM i.inst_opcode [CALLDATALOAD; GT; ISZERO; ASSERT; CALLDATACOPY] /\
    EVERY (\x. ?k. x = STRING #"%" (toString k) /\ k < st'.cs_next_var)
      i.inst_outputs) (emitted_insts st st')
Proof
  simp[compile_abi_decode_to_buf_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
    fresh_id_def, emit_def] >> rpt strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def] >> metis_tac[arithmeticTheory.LESS_ADD]
QED

Theorem entry_bytes_final_fresh[local]:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (DecBytestring n) st = ((),st') /\
  run_inst_seq (emitted_insts st st') s = OK t /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  fresh_vars_wrt limit_st t
Proof
  strip_tac >> drule entry_bytes_outputs >> strip_tac >>
  simp_tac bool_ss [fresh_vars_wrt_def] >> rpt strip_tac >>
  `FLOOKUP t.vs_vars (STRING #"%" (toString n')) =
   FLOOKUP s.vs_vars (STRING #"%" (toString n'))` by
    (irule entry_bytes_sequence_var >> goal_assum (drule_at Any) >>
     fs[EVERY_MEM] >> rpt strip_tac >> first_x_assum drule >> strip_tac >>
     qpat_x_assum `!x. MEM x i.inst_outputs ==> _` drule >>
     strip_tac >> gvs[] >> decide_tac) >>
  gvs[fresh_vars_wrt_def, FLOOKUP_DEF] >> metis_tac[]
QED

(* Endpoint contract used by the array callback: no child-entry freshness. *)
Theorem entry_canonical_bytes_endpoint[local]:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (DecBytestring n) st = ((),st') /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  LENGTH bs <= n /\ n < dimword (:256) /\
  sb + LENGTH (enc (Bytes NONE) (contractABI$BytesV bs)) < dimword (:256) /\
  d + abi_decode_bytes_copy_size n < dimword (:256) /\
  mem_bytes_at sb (LENGTH (enc (Bytes NONE) (contractABI$BytesV bs)))
    s.vs_call_ctx.cc_calldata = enc (Bytes NONE) (contractABI$BytesV bs) /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  fn_has_code st st' fn /\ ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
    t.vs_inst_idx = LENGTH st'.cs_current_insts /\ fresh_vars_wrt limit_st t /\
    val_in_memory (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV bs) d t.vs_memory /\
    abi_decode_frame d (abi_decode_bytes_copy_size n) s t /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    entry_loop_fields s t /\ abi_decode_sim ctx fn s t
Proof
  strip_tac >> drule_all entry_canonical_bytes_observed >> strip_tac >>
  drule_all entry_bytes_final_fresh >> strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_bytes_shape >> strip_tac >>
  `inst_extends st st'` by fs[inst_extends_def, rich_listTheory.IS_PREFIX_APPEND, emitted_insts_def,
      DROP_LENGTH_APPEND] >>
  drule_all abi_encoder_run_sequence_reach >> strip_tac >>
  drule_all abi_decoder_sequence_halted >> strip_tac >>
  qexists_tac `t with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  gvs[entry_loop_fields_def, fresh_vars_wrt_def, abi_decode_frame_def] >>
  asm_rewrite_tac[]
QED

Theorem entry_canonical_bytes_element_sequence[local]:
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info sf ce ty) (abi_embedded_static_size ce.ce_struct_fields ty)
    (type_memory_bytes ce ty) st = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops))
    CALLDATALOAD (Lit 0w) (DecBytestring n) middle = ((),last) /\
  type_to_abi_dec_info sf ce ty = DecBytestring n /\ n < dimword (:256) /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV avs) (ArrayV (DynArrayV xs)) /\
  j < LENGTH xs /\ is_dynamic (vyper_to_abi_type env ty) /\
  abi_decoder_ranges CALLDATALOAD (Lit 0w) src dst sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap s /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    (abi_decode_source CALLDATALOAD s) =
    enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  eval_operand ip s = SOME p /\ mload (w2n p) s = n2w j /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  middle.cs_next_var <= limit_st.cs_next_var /\ last.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st s ==>
  ?t. run_inst_seq (emitted_insts st last) s = OK t /\
    val_in_memory tv (EL j xs) (d+32+j*type_memory_bytes ce ty) t.vs_memory /\
    fresh_vars_wrt limit_st t /\ entry_loop_fields s t /\
    abi_decode_frame (d+32+j*type_memory_bytes ce ty) (type_memory_bytes ce ty) s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_halted = s.vs_halted /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op t = SOME w)
Proof
  strip_tac >>
  drule abi_decode_array_element_setup_operands >> strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  `inst_extends middle last` by
    (drule_all abi_decoder_bytes_shape >> strip_tac >>
     fs[inst_extends_def, rich_listTheory.IS_PREFIX_APPEND, emitted_insts_def,
        DROP_LENGTH_APPEND]) >>
  drule_all entry_canonical_dynamic_child_address >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st middle) s = OK prepared` >>
  drule_all ctor_actual_bytestring_metadata >> strip_tac >>
  `sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) < dimword (:256) /\
   d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) < dimword (:256)` by
    fs[abi_decoder_ranges_def] >>
  `sb + abi_array_child_offset NONE (vyper_to_abi_type env ty) avs j +
     LENGTH (enc (Bytes NONE) (contractABI$BytesV bs)) < dimword (:256) /\
   d+32+j*type_memory_bytes ce ty+abi_decode_bytes_copy_size n < dimword (:256)` by
    (gvs[Excl "enc_def"] >> decide_tac) >>
  `mem_bytes_at (sb + abi_array_child_offset NONE (vyper_to_abi_type env ty) avs j)
    (LENGTH (enc (Bytes NONE) (contractABI$BytesV bs))) prepared.vs_call_ctx.cc_calldata =
    enc (Bytes NONE) (contractABI$BytesV bs)` by fs[abi_decode_source_def] >>
  drule_all entry_canonical_bytes_observed >> strip_tac >>
  drule_all entry_bytes_final_fresh >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts middle last) prepared = OK t` >>
  `run_inst_seq (emitted_insts st last) s = OK t` by
    (irule run_inst_seq_compose_ok >> qexistsl_tac [`prepared`,`middle`] >> simp[]) >>
  drule_all abi_decoder_sequence_halted >> strip_tac >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  gvs[entry_loop_fields_def, abi_decoder_address_frame_def, abi_decode_frame_def,
      Excl "enc_def"] >> asm_rewrite_tac[] >> rpt strip_tac >>
  `abi_decoder_operand_live middle.cs_next_var op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  metis_tac[]
QED
