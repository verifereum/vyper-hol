(* Actual-state bridges for canonical arrays with bytestring elements. *)
Theory entryReachBodyCanonicalBytesArray
Ancestors
  valueEncodingDefs loweringStateRelDefs entryReachBodyCanonicalBytes entryReachBodyCanonicalChildAddress
  entryReachBodyExactArrayLoop entryReachBodyExactChildOwnership entryReachBodyArrayInit calldataBytesLeaf calldataDynOwned
  abiEncoderSequence abiDecoderExecution abiDecoderLoop abiDecoderLoopRegisters abiDecoderReentryPointer ctorAbiActualBytes
  abiDecoderTypedContract abiDecoderCoherence abiDecoderFrame abiDecoderFrameCompose abiDecoderDynamicLoopSetup
  abiDecoderArraySetupInputs abiDecoderArrayBackedge abiDecoderReentry venomMemProofs
  abiDecoderArrayLoopInit abiDecoderDynarrayPrefix abiDecoderGuards abiDecoderDynarrayBound
  fragExec abiDecoderArrayHeader abiDecoderIndexInit abiDecoderArrayInit abiDecoderPrimitiveLoopEntry
  abiDecoderLoopEmit abiDecoderAppend abiDecoderRecursiveLoopLayout abiDecoderRecursiveLoopEntry context
  abiDecoderLoopCode abiDecoderArraySetupCode abiDecoderCounters allocaFrontierBound
  abiDecoderBytesTyped abiDecoderContract abiEncoder emitHelper emitHelperProps exprLoweringProps compileEnv rich_list
  venomExecSemantics venomExecProofs venomState venomInst venomMemDefs valueEncoding valueEncodingProps words list arithmetic finite_map

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
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w) (DecBytestring n) st = ((),st') /\
  run_inst_seq (emitted_insts st st') s = OK t ==> entry_loop_fields s t
Proof
  strip_tac >>
  `EVERY (\i. MEM i.inst_opcode [CALLDATALOAD; GT; ISZERO; ASSERT; CALLDATACOPY])
    (emitted_insts st st')` by
    (qpat_x_assum `compile_abi_decode_to_buf _ _ _ (Lit 0w) _ _ _ = _` mp_tac >>
     simp[compile_abi_decode_to_buf_def, compile_abi_dec_addr_def, compile_abi_decode_range_check_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def] >> rpt strip_tac >> gvs[emitted_insts_def] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
     simp[DROP_LENGTH_APPEND, mk_inst_def]) >>
  drule_all entry_bytes_sequence_fields >> simp[]
QED

Theorem entry_canonical_bytes_observed[local]:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w) (DecBytestring n) st = ((),st') /\
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
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w) (DecBytestring n) st = ((),st') ==>
  EVERY (\i. MEM i.inst_opcode [CALLDATALOAD; GT; ISZERO; ASSERT; CALLDATACOPY] /\
    EVERY (\x. ?k. x = STRING #"%" (toString k) /\ k < st'.cs_next_var)
      i.inst_outputs) (emitted_insts st st')
Proof
  simp[compile_abi_decode_to_buf_def, compile_abi_dec_addr_def, compile_abi_decode_range_check_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
    fresh_id_def, emit_def] >> rpt strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def] >> metis_tac[arithmeticTheory.LESS_ADD]
QED

Theorem entry_bytes_final_fresh[local]:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w) (DecBytestring n) st = ((),st') /\
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
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w) (DecBytestring n) st = ((),st') /\
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

Theorem entry_bytes_element_shape[local]:
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) (Lit 0w) di az mz st = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops))
    CALLDATALOAD (Lit 0w) (Lit 0w) (DecBytestring n) middle = ((),last) ==>
  last.cs_blocks = st.cs_blocks /\ last.cs_current_bb = st.cs_current_bb /\
  inst_extends st last /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st last)
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_element_setup_shape >> strip_tac >>
  drule_all abi_decoder_bytes_shape >> strip_tac >>
  `inst_extends st middle /\ inst_extends middle last` by
    (conj_tac
     >- (qpat_x_assum `isPREFIX middle.cs_current_insts last.cs_current_insts` kall_tac >>
         fs[inst_extends_def, IS_PREFIX_APPEND, emitted_insts_def, DROP_LENGTH_APPEND]) >>
     qpat_x_assum `isPREFIX st.cs_current_insts middle.cs_current_insts` kall_tac >>
     fs[inst_extends_def, IS_PREFIX_APPEND, emitted_insts_def, DROP_LENGTH_APPEND]) >>
  `inst_extends st last` by metis_tac[inst_extends_trans] >>
  `emitted_insts st last = emitted_insts st middle ++ emitted_insts middle last` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  asm_rewrite_tac[EVERY_APPEND]
QED

Theorem entry_canonical_bytes_element_sequence[local]:
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce ty) (abi_embedded_static_size ce.ce_struct_fields ty)
    (type_memory_bytes ce ty) st = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops))
    CALLDATALOAD (Lit 0w) (Lit 0w) (DecBytestring n) middle = ((),last) /\
  type_to_abi_dec_info sf ce ty = DecBytestring n /\ n < dimword (:256) /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV avs) (ArrayV (DynArrayV xs)) /\
  j < LENGTH xs /\ is_dynamic (vyper_to_abi_type env ty) /\
  abi_decoder_ranges CALLDATALOAD (Lit 0w) (Lit 0w) src dst 0 sb
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
    t.vs_halted = s.vs_halted /\ eval_operand (FST ops) t = SOME (n2w j) /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op t = SOME w) /\
    (!ctx fn. fn_has_code st last fn /\ ~s.vs_halted /\
      s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts ==>
      t.vs_current_bb = last.cs_current_bb /\
      abi_decode_sim ctx fn s (t with vs_inst_idx := LENGTH last.cs_current_insts))
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
  `eval_operand (FST ops) t = SOME (n2w j)` by metis_tac[] >>
  `!ctx fn. fn_has_code st last fn /\ ~s.vs_halted /\
      s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts ==>
      t.vs_current_bb = last.cs_current_bb /\
      abi_decode_sim ctx fn s (t with vs_inst_idx := LENGTH last.cs_current_insts)` by
    (rpt strip_tac >> drule_all entry_bytes_element_shape >> strip_tac >>
     drule_all abi_encoder_run_sequence_reach >> simp[]) >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  gvs[entry_loop_fields_def, abi_decoder_address_frame_def, abi_decode_frame_def,
      Excl "enc_def"] >> asm_rewrite_tac[] >> rpt strip_tac >>
  `abi_decoder_operand_live middle.cs_next_var op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  metis_tac[]
QED

(* The loop invariant records only the initialized parent's stable interface.
   Index, ncounter contents, PC and haltedness live in the exact loop shell. *)
Definition entry_bytes_array_inv_def:
  entry_bytes_array_inv next limit_st d outsz q ncount prepared u <=>
    u.vs_allocas = prepared.vs_allocas /\ u.vs_alloca_next = prepared.vs_alloca_next /\
    entry_loop_fields prepared u /\ fresh_vars_wrt limit_st u /\
    (!op w. abi_decoder_operand_live next op /\ eval_operand op prepared = SOME w ==>
      eval_operand op u = SOME w) /\
    abi_decode_footprint_frame [(d,outsz);(q,32)] prepared u /\
    mem_word_at d u.vs_memory = n2w ncount
End

Theorem entry_bytes_array_inv_init:
  fresh_vars_wrt limit_st prepared /\ mem_word_at d prepared.vs_memory = n2w ncount ==>
  entry_bytes_array_inv next limit_st d outsz q ncount prepared prepared
Proof
  simp[entry_bytes_array_inv_def, entry_loop_fields_def, abi_decode_footprint_frame_refl]
QED

Theorem entry_bytes_array_inv_header:
  next + 4 <= limit_st.cs_next_var /\
  entry_bytes_array_inv next limit_st d outsz q ncount prepared u ==>
  entry_bytes_array_inv next limit_st d outsz q ncount prepared
    (jump_to lbl (abi_decode_header_state (STRING #"%" (toString next))
      (STRING #"%" (toString (next+1))) (STRING #"%" (toString (next+2)))
      (STRING #"%" (toString (next+3))) j n u))
Proof
  simp_tac bool_ss [entry_bytes_array_inv_def] >> strip_tac >>
  drule_all abi_decoder_header_registers >>
  disch_then (qspecl_then [`n`,`j`] strip_assume_tac) >>
  asm_simp_tac (srw_ss()) [] >>
  fs[entry_loop_fields_def, abi_decode_footprint_frame_def,
    jump_to_def, abi_decode_header_state_def, update_var_def]
QED

Theorem entry_bytes_array_inv_backedge:
  next <= nv /\ nv < limit_st.cs_next_var /\ (d+32 <= q \/ q+32 <= d) /\
  entry_bytes_array_inv next limit_st d outsz q ncount prepared u ==>
  entry_bytes_array_inv next limit_st d outsz q ncount prepared
    (jump_to hdr (mstore q w (update_var (STRING #"%" (toString nv)) v u)))
Proof
  simp_tac bool_ss [entry_bytes_array_inv_def] >> strip_tac >>
  drule_all abi_decoder_generated_update_fresh >> disch_then (qspec_then `v` assume_tac) >>
  `!op w. abi_decoder_operand_live next op /\ eval_operand op prepared = SOME w ==>
    eval_operand op (update_var (STRING #"%" (toString nv)) v u) = SOME w` by
    (rpt strip_tac >>
     `abi_decoder_operand_live nv op` by
       (irule abi_decoder_operand_live_mono >> qexists_tac `next` >> simp[]) >>
     simp[abi_decoder_generated_update_operand]) >>
  `abi_decode_footprint_frame [(d,outsz);(q,32)] prepared
      (mstore q w (update_var (STRING #"%" (toString nv)) v u))` by
    (irule abi_decode_footprint_frame_trans >> qexists_tac `u` >> simp[] >>
     simp[abi_decode_footprint_frame_def] >> rpt strip_tac >>
     `abi_footprint_disjoint p n [(q,32)]` by fs[abi_footprint_disjoint_def] >>
     mp_tac (Q.SPECL [`p`,`n`,`q`,`w`,`u`] mstore_mem_bytes_at_disjoint) >>
     fs[abi_footprint_disjoint_def, mstore_def, update_var_def,
        write_memory_with_expansion_def]) >>
  `mem_word_at d (mstore q w (update_var (STRING #"%" (toString nv)) v u)).vs_memory = n2w ncount` by
    (asm_simp_tac (srw_ss()) [mstore_mem_word_at_disjoint, update_var_def]) >>
  asm_simp_tac (srw_ss()) [eval_operand_mstore, fresh_vars_wrt_def, lookup_var_def] >>
  fs[entry_loop_fields_def, abi_decode_footprint_frame_def, jump_to_def,
     mstore_def, write_memory_with_expansion_def, update_var_def, fresh_vars_wrt_def,
     lookup_var_def]
QED

Theorem entry_bytes_array_inv_child:
  entry_bytes_array_inv next limit_st d outsz q ncount prepared u /\
  t.vs_allocas = u.vs_allocas /\ t.vs_alloca_next = u.vs_alloca_next /\
  entry_loop_fields u t /\ fresh_vars_wrt limit_st t /\
  next <= child_next /\
  (!op w. abi_decoder_operand_live child_next op /\ eval_operand op u = SOME w ==>
    eval_operand op t = SOME w) /\
  abi_decode_frame cell sz u t /\ d+32 <= cell /\ cell+sz <= d+outsz ==>
  entry_bytes_array_inv next limit_st d outsz q ncount prepared t
Proof
  simp_tac bool_ss [entry_bytes_array_inv_def] >> strip_tac >>
  `mem_word_at d t.vs_memory = mem_word_at d u.vs_memory` by
    (irule abi_decode_frame_mem_word >> goal_assum (drule_at Any) >> simp[]) >>
  `abi_decode_footprint_frame [(d,outsz);(q,32)] u t` by
    (irule abi_decode_footprint_frame_weaken >> qexists_tac `[(cell,sz)]` >>
     simp[GSYM abi_decode_frame_footprint] >> qexistsl_tac [`d`,`outsz`] >> simp[]) >>
  `abi_decode_footprint_frame [(d,outsz);(q,32)] prepared t` by
    metis_tac[abi_decode_footprint_frame_trans] >>
  asm_rewrite_tac[] >> conj_tac
  >- fs[entry_loop_fields_def] >>
  rpt strip_tac >>
  `abi_decoder_operand_live child_next op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `next` >> simp[]) >>
  metis_tac[]
QED

(* Readiness supplies the ncounter observation; it is not inferred from J. *)
Theorem entry_bytes_header_inputs:
  abi_decode_loop_ready hdr ip src CALLDATALOAD p srcaddr ncount j s /\
  abi_decoder_ranges CALLDATALOAD (Lit 0w) (Lit 0w) src dst 0 sb len d outsz b cap s /\
  abi_decoder_operand_live next ip /\ abi_decoder_operand_live next src /\
  abi_decoder_operand_live next dst /\
  next + 4 <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  h = jump_to body_lbl (abi_decode_header_state (STRING #"%" (toString next))
    (STRING #"%" (toString (next+1))) (STRING #"%" (toString (next+2)))
    (STRING #"%" (toString (next+3))) j ncount s) ==>
  eval_operand ip h = SOME p /\ mload (w2n p) h = n2w j /\
  abi_decoder_ranges CALLDATALOAD (Lit 0w) (Lit 0w) src dst 0 sb len d outsz b cap h /\
  fresh_vars_wrt limit_st h /\ h.vs_call_ctx = s.vs_call_ctx /\
  ~h.vs_halted /\ h.vs_current_bb = body_lbl /\ h.vs_inst_idx = 0
Proof
  strip_tac >> drule_all abi_decoder_header_registers >>
  disch_then (qspecl_then [`ncount`,`j`] strip_assume_tac) >>
  gvs[abi_decode_loop_ready_def, abi_decoder_ranges_def] >>
  asm_simp_tac (srw_ss()) [] >>
  fs[jump_to_def, abi_decode_header_state_def, update_var_def, mload_def]
QED

Theorem entry_bytes_element_after_header[local]:
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce ty) (abi_embedded_static_size ce.ce_struct_fields ty)
    (type_memory_bytes ce ty) st = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops))
    CALLDATALOAD (Lit 0w) (Lit 0w) (DecBytestring n) middle = ((),last) /\
  type_to_abi_dec_info sf ce ty = DecBytestring n /\ n < dimword (:256) /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV avs) (ArrayV (DynArrayV xs)) /\
  j < LENGTH xs /\ is_dynamic (vyper_to_abi_type env ty) /\
  abi_decoder_ranges CALLDATALOAD (Lit 0w) (Lit 0w) src dst 0 sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap s /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    (abi_decode_source CALLDATALOAD s) =
    enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  abi_decode_loop_ready hdr ip src CALLDATALOAD p srcaddr (LENGTH xs) j s /\
  abi_decoder_operand_live next ip /\ abi_decoder_operand_live next src /\
  abi_decoder_operand_live next dst /\ next <= st.cs_next_var /\
  next + 4 <= limit_st.cs_next_var /\
  middle.cs_next_var <= limit_st.cs_next_var /\ last.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st s /\
  h = jump_to body_lbl (abi_decode_header_state (STRING #"%" (toString next))
    (STRING #"%" (toString (next+1))) (STRING #"%" (toString (next+2)))
    (STRING #"%" (toString (next+3))) j (LENGTH xs) s) ==>
  ?t. run_inst_seq (emitted_insts st last) h = OK t /\
    val_in_memory tv (EL j xs) (d+32+j*type_memory_bytes ce ty) t.vs_memory /\
    fresh_vars_wrt limit_st t /\ entry_loop_fields h t /\
    abi_decode_frame (d+32+j*type_memory_bytes ce ty) (type_memory_bytes ce ty) h t /\
    t.vs_allocas = h.vs_allocas /\ t.vs_alloca_next = h.vs_alloca_next /\
    ~t.vs_halted /\ eval_operand (FST ops) t = SOME (n2w j) /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op h = SOME w ==>
      eval_operand op t = SOME w) /\
    (!ctx fn. fn_has_code st last fn /\ st.cs_current_bb = body_lbl /\
      st.cs_current_insts = [] ==>
      t.vs_current_bb = last.cs_current_bb /\
      abi_decode_sim ctx fn h (t with vs_inst_idx := LENGTH last.cs_current_insts))
Proof
  strip_tac >> drule_all entry_bytes_header_inputs >> strip_tac >>
  `mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    (abi_decode_source CALLDATALOAD h) =
    enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)` by
    fs[abi_decode_source_def] >>
  `abi_decoder_operand_live st.cs_next_var src /\
   abi_decoder_operand_live st.cs_next_var dst` by
    (conj_tac >> irule abi_decoder_operand_live_mono >> qexists_tac `next` >> simp[]) >>
  drule_all entry_canonical_bytes_element_sequence >> strip_tac >>
  goal_assum (drule_at Any) >> asm_rewrite_tac[] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!ctx fn. _` (qspecl_then [`ctx`,`fn`] mp_tac) >>
  (impl_tac >- simp[]) >> simp[]
QED

Theorem entry_bytes_element_invariant[local]:
  entry_bytes_array_inv next limit_st d outsz q (LENGTH xs) prepared h /\
  entry_loop_prefix tv xs d j h /\ j < LENGTH xs /\ EVERY (val_wf tv) xs /\
  FLOOKUP h.vs_allocas oid = SOME (d,capacity) /\
  32+j*type_memory_size tv <= capacity /\ alloca_inv t /\
  t.vs_allocas = h.vs_allocas /\ t.vs_alloca_next = h.vs_alloca_next /\
  entry_loop_fields h t /\ fresh_vars_wrt limit_st t /\ next <= child_next /\
  (!op w. abi_decoder_operand_live child_next op /\ eval_operand op h = SOME w ==>
    eval_operand op t = SOME w) /\
  abi_decode_frame (d+32+j*type_memory_size tv) (type_memory_size tv) h t /\
  d+32+j*type_memory_size tv+type_memory_size tv <= d+outsz /\
  val_in_memory tv (EL j xs) (d+32+j*type_memory_size tv) t.vs_memory ==>
  entry_bytes_array_inv next limit_st d outsz q (LENGTH xs) prepared t /\
  entry_loop_prefix tv xs d (SUC j) t
Proof
  strip_tac >> conj_tac
  >- (irule entry_bytes_array_inv_child >> goal_assum (drule_at Any) >>
      qexistsl_tac [`d+32+j*type_memory_size tv`,`child_next`,`type_memory_size tv`,`h`] >>
      simp[]) >>
  irule entry_child_exact_prefix_extend >> asm_rewrite_tac[] >>
  qexistsl_tac [`capacity`,`0`,`0`,`oid`,`h`,`[]`] >>
  simp[GSYM abi_decode_frame_footprint]
QED

Theorem entry_bytes_array_backedge[local]:
  entry_loop_child_end fn tail prefix bid iv (STRING #"%" (toString nv))
    ip hdr src p srcaddr (LENGTH xs) j t /\
  lookup_block hdr fn.fn_blocks = SOME hdr_bb /\
  phi_prefix_length hdr_bb.bb_instructions = 0 /\
  entry_bytes_array_inv next limit_st d outsz (w2n p) (LENGTH xs) prepared t /\
  entry_loop_prefix tv xs d (SUC j) t /\ EVERY (val_wf tv) xs /\
  j < LENGTH xs /\ LENGTH xs < dimword (:256) /\
  abi_decoder_operand_live next ip /\ abi_decoder_operand_live next src /\
  next <= nv /\ nv < limit_st.cs_next_var /\
  (d+32 <= w2n p \/ w2n p+32 <= d) /\
  (!k. k < SUC j ==> w2n p+32 <= d+32+k*type_memory_size tv \/
    d+32+k*type_memory_size tv+type_memory_size tv <= w2n p) ==>
  ?v. abi_decode_loop_ready hdr ip src CALLDATALOAD p srcaddr (LENGTH xs) (SUC j) v /\
    entry_bytes_array_inv next limit_st d outsz (w2n p) (LENGTH xs) prepared v /\
    entry_loop_prefix tv xs d (SUC j) v /\ entry_loop_fields t v /\
    abi_decode_sim ctx fn t v /\
    v = jump_to hdr (mstore (w2n p) (n2w (SUC j))
      (update_var (STRING #"%" (toString nv)) (n2w (SUC j)) t))
Proof
  strip_tac >>
  `abi_decoder_operand_live nv ip /\ abi_decoder_operand_live nv src` by
    (conj_tac >> irule abi_decoder_operand_live_mono >> qexists_tac `next` >> simp[]) >>
  `ip <> Var (STRING #"%" (toString nv))` by
    (irule abi_decoder_live_excludes_output >> qexists_tac `next` >> simp[]) >>
  qabbrev_tac `v = jump_to hdr (mstore (w2n p) (n2w (SUC j))
    (update_var (STRING #"%" (toString nv)) (n2w (SUC j)) t))` >>
  `entry_bytes_array_inv next limit_st d outsz (w2n p) (LENGTH xs) prepared v` by
    (simp[Abbr `v`] >> irule entry_bytes_array_inv_backedge >> simp[]) >>
  `abi_decode_sim ctx fn t v` by
    (simp[Abbr `v`] >> irule abi_decode_backedge_sim >>
     fs[entry_loop_child_end_def] >> metis_tac[]) >>
  `eval_operand ip v = SOME p /\ eval_operand src v = SOME srcaddr` by
    (fs[entry_loop_child_end_def, Abbr `v`, eval_operand_mstore,
        abi_decoder_generated_update_operand]) >>
  `abi_decode_loop_ready hdr ip src CALLDATALOAD p srcaddr (LENGTH xs) (SUC j) v` by
    (fs[entry_loop_child_end_def, abi_decode_loop_ready_def, Abbr `v`,
      abi_decode_mload_jump, mload_mstore_same_proof, abi_decode_load_def,
      abi_decode_source_def, jump_to_def, mstore_def, update_var_def,
      write_memory_with_expansion_def]) >>
  `entry_loop_prefix tv xs d (SUC j) v` by
    (simp_tac bool_ss [entry_loop_prefix_def] >> rpt strip_tac >>
     `val_wf tv (EL k xs)` by
       (fs[EVERY_EL] >> first_x_assum irule >> decide_tac) >>
     `val_in_memory tv (EL k xs) (d+32+k*type_memory_size tv) t.vs_memory` by
       fs[entry_loop_prefix_def] >>
     `val_in_memory tv (EL k xs) (d+32+k*type_memory_size tv)
       (mstore (w2n p) (n2w (SUC j)) (t with vs_memory := t.vs_memory)).vs_memory` by
       (irule (cj 1 mstore_preserves_val_in_memory) >> simp[]) >>
     gvs[Abbr `v`, jump_to_def, mstore_def, update_var_def, write_memory_with_expansion_def]) >>
  qexists_tac `v` >> asm_rewrite_tac[] >>
  simp[Abbr `v`, entry_loop_fields_def, jump_to_def, mstore_def,
    update_var_def, write_memory_with_expansion_def]
QED

(* Fixed canonical/compiler facts are separated from the indexed live state.
   Sizes have one normal form here: the parent allocation size and tv stride. *)
Definition entry_bytes_array_config_def:
  entry_bytes_array_config
    ((ce,env,sf,ty,tv,maxn,parent_di,avs,xs,n),
     (ip,src,dst,ops,st,middle,last,limit_st),
     (next,d,p,srcaddr,sb,b,cap,oid,capacity),
     ((ctx:venom_context),fn,hdr,body_lbl,exit_lbl,hid,tail,prefix,bid,iv,nv)) <=>
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce ty) (abi_embedded_static_size ce.ce_struct_fields ty)
    (type_memory_bytes ce ty) st = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops))
    CALLDATALOAD (Lit 0w) (Lit 0w) (DecBytestring n) middle = ((),last) /\
  type_to_abi_dec_info sf ce ty = DecBytestring n /\ n < dimword (:256) /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV avs) (ArrayV (DynArrayV xs)) /\
  is_dynamic (vyper_to_abi_type env ty) /\
  type_memory_bytes ce ty = type_memory_size tv /\
  EVERY (val_wf tv) xs /\ LENGTH xs < dimword (:256) /\ LENGTH xs <= maxn /\
  abi_decoder_operand_live next ip /\ abi_decoder_operand_live next src /\
  abi_decoder_operand_live next dst /\ next <= st.cs_next_var /\
  next + 4 <= limit_st.cs_next_var /\
  middle.cs_next_var <= limit_st.cs_next_var /\ last.cs_next_var <= limit_st.cs_next_var /\
  st.cs_current_bb = body_lbl /\ st.cs_current_insts = [] /\ fn_has_code st last fn /\
  abi_decode_loop_cfg fn hdr body_lbl exit_lbl hid ip src CALLDATALOAD
    (STRING #"%" (toString next)) (STRING #"%" (toString (next+1)))
    (STRING #"%" (toString (next+2))) (STRING #"%" (toString (next+3))) /\
  src <> Var (STRING #"%" (toString next)) /\
  STRING #"%" (toString next) <> STRING #"%" (toString (next+1)) /\
  (?bb. lookup_block tail fn.fn_blocks = SOME bb /\
    bb.bb_instructions = prefix ++ abi_decode_backedge_insts bid iv
      (STRING #"%" (toString nv)) ip hdr) /\
  last.cs_current_bb = tail /\ last.cs_current_insts = prefix /\
  FST ops = Var iv /\
  next <= nv /\ nv < limit_st.cs_next_var /\
  (d+32 <= w2n p \/ w2n p+32 <= d) /\
  (!k. k < LENGTH xs ==>
    32+k*type_memory_size tv <= capacity /\
    d+32+k*type_memory_size tv+type_memory_size tv <=
      d+type_memory_bytes ce (ArrayT ty (Dynamic maxn)) /\
    (w2n p+32 <= d+32+k*type_memory_size tv \/
     d+32+k*type_memory_size tv+type_memory_size tv <= w2n p))
End

Definition entry_bytes_array_state_def:
  entry_bytes_array_state
    ((ce,env,sf,ty,tv,maxn,parent_di,avs,xs,n),
     (ip,src,dst,ops,st,middle,last,limit_st),
     (next,d,p,srcaddr,sb,b,cap,oid,capacity),
     (ctx,fn,hdr,body_lbl,exit_lbl,hid,tail,prefix,bid,iv,nv)) prepared j s <=>
  abi_decode_loop_ready hdr ip src CALLDATALOAD p srcaddr (LENGTH xs) j s /\
  entry_bytes_array_inv next limit_st d (type_memory_bytes ce (ArrayT ty (Dynamic maxn)))
    (w2n p) (LENGTH xs) prepared s /\
  entry_loop_prefix tv xs d j s /\ j <= LENGTH xs /\ alloca_inv s /\
  FLOOKUP s.vs_allocas oid = SOME (d,capacity) /\
  abi_decoder_ranges CALLDATALOAD (Lit 0w) (Lit 0w) src dst 0 sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap s /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    (abi_decode_source CALLDATALOAD s) =
    enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)
End

Theorem entry_bytes_array_config_child[local]:
  cfg = ((ce,env,sf,ty,tv,maxn,parent_di,avs,xs,n),
       (ip,src,dst,ops,st,middle,last,limit_st),
       (next,d,p,srcaddr,sb,b,cap,oid,capacity),
       (ctx,fn,hdr,body_lbl,exit_lbl,hid,tail,prefix,bid,iv,nv)) /\
  entry_bytes_array_config cfg /\ entry_bytes_array_state cfg prepared j s /\
  j < LENGTH xs /\
  h = jump_to body_lbl (abi_decode_header_state (STRING #"%" (toString next))
    (STRING #"%" (toString (next+1))) (STRING #"%" (toString (next+2)))
    (STRING #"%" (toString (next+3))) j (LENGTH xs) s) ==>
  ?t. run_inst_seq (emitted_insts st last) h = OK t /\
    val_in_memory tv (EL j xs) (d+32+j*type_memory_size tv) t.vs_memory /\
    fresh_vars_wrt limit_st t /\ entry_loop_fields h t /\
    abi_decode_frame (d+32+j*type_memory_size tv) (type_memory_size tv) h t /\
    t.vs_allocas = h.vs_allocas /\ t.vs_alloca_next = h.vs_alloca_next /\
    ~t.vs_halted /\ eval_operand (Var iv) t = SOME (n2w j) /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op h = SOME w ==>
      eval_operand op t = SOME w) /\
    t.vs_current_bb = tail /\
    abi_decode_sim ctx fn h (t with vs_inst_idx := LENGTH prefix)
Proof
  strip_tac >> qpat_x_assum `cfg = _` SUBST_ALL_TAC >>
  qpat_x_assum `entry_bytes_array_config _`
    (strip_assume_tac o PURE_REWRITE_RULE [entry_bytes_array_config_def]) >>
  qpat_x_assum `entry_bytes_array_state _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [entry_bytes_array_state_def]) >>
  `fresh_vars_wrt limit_st s` by fs[entry_bytes_array_inv_def] >>
  drule_all entry_bytes_element_after_header >> strip_tac >>
  qpat_x_assum `!ctx fn. _` (qspecl_then [`ctx`,`fn`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  goal_assum (drule_at Any) >> gvs[]
QED

Theorem entry_bytes_array_config_header[local]:
  cfg = ((ce,env,sf,ty,tv,maxn,parent_di,avs,xs,n),
       (ip,src,dst,ops,st,middle,last,limit_st),
       (next,d,p,srcaddr,sb,b,cap,oid,capacity),
       (ctx,fn,hdr,body_lbl,exit_lbl,hid,tail,prefix,bid,iv,nv)) /\
  entry_bytes_array_config cfg /\ entry_bytes_array_state cfg prepared j s /\
  j < LENGTH xs /\
  h = jump_to body_lbl (abi_decode_header_state (STRING #"%" (toString next))
    (STRING #"%" (toString (next+1))) (STRING #"%" (toString (next+2)))
    (STRING #"%" (toString (next+3))) j (LENGTH xs) s) ==>
  entry_bytes_array_inv next limit_st d (type_memory_bytes ce (ArrayT ty (Dynamic maxn)))
    (w2n p) (LENGTH xs) prepared h /\ entry_loop_prefix tv xs d j h /\
  alloca_inv h /\ FLOOKUP h.vs_allocas oid = SOME (d,capacity) /\
  eval_operand ip h = SOME p /\ eval_operand src h = SOME srcaddr /\
  entry_loop_fields s h /\ abi_decode_sim ctx fn s h /\
  (!op. abi_decoder_operand_live next op ==> eval_operand op h = eval_operand op s) /\
  next <= st.cs_next_var
Proof
  strip_tac >> qpat_x_assum `cfg = _` SUBST_ALL_TAC >>
  qpat_x_assum `entry_bytes_array_config _`
    (strip_assume_tac o PURE_REWRITE_RULE [entry_bytes_array_config_def]) >>
  qpat_x_assum `entry_bytes_array_state _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [entry_bytes_array_state_def]) >>
  `fresh_vars_wrt limit_st s` by fs[entry_bytes_array_inv_def] >>
  `entry_bytes_array_inv next limit_st d (type_memory_bytes ce (ArrayT ty (Dynamic maxn)))
    (w2n p) (LENGTH xs) prepared h` by
    (asm_rewrite_tac[] >> irule entry_bytes_array_inv_header >> simp[]) >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  `abi_decode_sim ctx fn s h` by
    (drule_all abi_decode_ready_header_sim >> simp[]) >>
  drule_all abi_decoder_header_registers >>
  disch_then (qspecl_then [`LENGTH xs`,`j`] strip_assume_tac) >>
  `eval_operand ip h = SOME p /\ eval_operand src h = SOME srcaddr` by
    (asm_simp_tac (srw_ss()) [abi_decoder_operand_jump] >>
     fs[abi_decode_loop_ready_def]) >>
  `alloca_inv h` by
    (qpat_x_assum `h = _` SUBST1_TAC >>
     qpat_x_assum `alloca_inv s` mp_tac >>
     simp_tac (srw_ss()) [alloca_inv_def, allocas_non_overlapping_def,
       alloca_next_valid_def, jump_to_def, abi_decode_header_state_def, update_var_def]) >>
  `!op. abi_decoder_operand_live next op ==> eval_operand op h = eval_operand op s` by
    asm_simp_tac (srw_ss()) [abi_decoder_operand_jump] >>
  asm_rewrite_tac[] >>
  gvs[entry_loop_prefix_def, entry_loop_fields_def,
    abi_decode_header_state_def, jump_to_def, update_var_def]
QED

Theorem entry_bytes_array_state_transfer[local]:
  cfg = ((ce,env,sf,ty,tv,maxn,parent_di,avs,xs,n),
       (ip,src,dst,ops,st,middle,last,limit_st),
       (next,d,p,srcaddr,sb,b,cap,oid,capacity),
       (ctx,fn,hdr,body_lbl,exit_lbl,hid,tail,prefix,bid,iv,nv)) /\
  entry_bytes_array_config cfg /\ entry_bytes_array_state cfg prepared j s /\
  entry_bytes_array_inv next limit_st d (type_memory_bytes ce (ArrayT ty (Dynamic maxn)))
    (w2n p) (LENGTH xs) prepared t /\
  abi_decode_loop_ready hdr ip src CALLDATALOAD p srcaddr (LENGTH xs) k t /\
  entry_loop_prefix tv xs d k t /\ k <= LENGTH xs /\
  entry_loop_fields s t /\ t.vs_allocas = s.vs_allocas /\
  t.vs_alloca_next = s.vs_alloca_next /\
  (!op w. abi_decoder_operand_live next op /\ eval_operand op s = SOME w ==>
     eval_operand op t = SOME w) ==>
  entry_bytes_array_state cfg prepared k t
Proof
  strip_tac >> qpat_x_assum `cfg = _` SUBST_ALL_TAC >>
  qpat_x_assum `entry_bytes_array_config _`
    (strip_assume_tac o PURE_REWRITE_RULE [entry_bytes_array_config_def]) >>
  qpat_x_assum `entry_bytes_array_state _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [entry_bytes_array_state_def]) >>
  pure_rewrite_tac[entry_bytes_array_state_def] >> asm_rewrite_tac[] >>
  `alloca_inv t` by
    (qpat_x_assum `alloca_inv s` mp_tac >>
     asm_simp_tac (srw_ss()) [alloca_inv_def, allocas_non_overlapping_def,
       alloca_next_valid_def]) >>
  `t.vs_call_ctx = s.vs_call_ctx` by
    fs[entry_loop_fields_def] >>
  asm_rewrite_tac[] >>
  fs[abi_decoder_ranges_def, abi_decode_source_def] >>
  metis_tac[]
QED

Theorem entry_bytes_array_child_memory[local]:
  cfg = ((ce,env,sf,ty,tv,maxn,parent_di,avs,xs,n),
       (ip,src,dst,ops,st,middle,last,limit_st),
       (next,d,p,srcaddr,sb,b,cap,oid,capacity),
       (ctx,fn,hdr,body_lbl,exit_lbl,hid,tail,prefix,bid,iv,nv)) /\
  entry_bytes_array_config cfg /\ entry_bytes_array_state cfg prepared j s /\
  j < LENGTH xs /\
  h = jump_to body_lbl (abi_decode_header_state (STRING #"%" (toString next))
    (STRING #"%" (toString (next+1))) (STRING #"%" (toString (next+2)))
    (STRING #"%" (toString (next+3))) j (LENGTH xs) s) /\
  val_in_memory tv (EL j xs) (d+32+j*type_memory_size tv) t.vs_memory /\
  fresh_vars_wrt limit_st t /\ entry_loop_fields h t /\
  abi_decode_frame (d+32+j*type_memory_size tv) (type_memory_size tv) h t /\
  t.vs_allocas = h.vs_allocas /\ t.vs_alloca_next = h.vs_alloca_next /\
  (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op h = SOME w ==>
    eval_operand op t = SOME w) ==>
  entry_bytes_array_inv next limit_st d (type_memory_bytes ce (ArrayT ty (Dynamic maxn)))
    (w2n p) (LENGTH xs) prepared t /\ entry_loop_prefix tv xs d (SUC j) t
Proof
  strip_tac >> drule_all entry_bytes_array_config_header >> strip_tac >>
  qpat_x_assum `cfg = _` SUBST_ALL_TAC >>
  qpat_x_assum `entry_bytes_array_config _`
    (strip_assume_tac o PURE_REWRITE_RULE [entry_bytes_array_config_def]) >>
  `alloca_inv t` by
    (qpat_x_assum `alloca_inv h` mp_tac >>
     asm_simp_tac (srw_ss()) [alloca_inv_def, allocas_non_overlapping_def,
       alloca_next_valid_def]) >>
  `32+j*type_memory_size tv <= capacity /\
   d+32+j*type_memory_size tv+type_memory_size tv <=
      d+type_memory_bytes ce (ArrayT ty (Dynamic maxn))` by simp[] >>
  drule_all entry_bytes_element_invariant >> simp[]
QED

Theorem entry_bytes_array_child_tail[local]:
  cfg = ((ce,env,sf,ty,tv,maxn,parent_di,avs,xs,n),
       (ip,src,dst,ops,st,middle,last,limit_st),
       (next,d,p,srcaddr,sb,b,cap,oid,capacity),
       (ctx,fn,hdr,body_lbl,exit_lbl,hid,tail,prefix,bid,iv,nv)) /\
  entry_bytes_array_config cfg /\ entry_bytes_array_state cfg prepared j s /\
  j < LENGTH xs /\
  h = jump_to body_lbl (abi_decode_header_state (STRING #"%" (toString next))
    (STRING #"%" (toString (next+1))) (STRING #"%" (toString (next+2)))
    (STRING #"%" (toString (next+3))) j (LENGTH xs) s) /\
  ~t.vs_halted /\ t.vs_current_bb = tail /\
  eval_operand (Var iv) t = SOME (n2w j) /\ entry_loop_fields h t /\
  (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op h = SOME w ==>
    eval_operand op t = SOME w) ==>
  entry_loop_child_end fn tail prefix bid iv (STRING #"%" (toString nv))
    ip hdr src p srcaddr (LENGTH xs) j (t with vs_inst_idx := LENGTH prefix)
Proof
  strip_tac >> drule_all entry_bytes_array_config_header >> strip_tac >>
  qpat_x_assum `cfg = _` SUBST_ALL_TAC >>
  qpat_x_assum `entry_bytes_array_config _`
    (strip_assume_tac o PURE_REWRITE_RULE [entry_bytes_array_config_def]) >>
  qpat_x_assum `entry_bytes_array_state _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [entry_bytes_array_state_def]) >>
  `abi_decoder_operand_live st.cs_next_var ip /\
   abi_decoder_operand_live st.cs_next_var src` by
    (conj_tac >> irule abi_decoder_operand_live_mono >> qexists_tac `next` >> simp[]) >>
  `eval_operand ip t = SOME p /\ eval_operand src t = SOME srcaddr` by metis_tac[] >>
  `t.vs_call_ctx = s.vs_call_ctx` by fs[entry_loop_fields_def] >>
  `abi_decode_load CALLDATALOAD srcaddr t = n2w (LENGTH xs)` by
    fs[abi_decode_loop_ready_def, abi_decode_load_def, abi_decode_source_def] >>
  fs[entry_loop_child_end_def, eval_operand_def, lookup_var_def,
    abi_decode_load_def, abi_decode_source_def] >> metis_tac[]
QED

Theorem entry_bytes_array_config_backedge[local]:
  cfg = ((ce,env,sf,ty,tv,maxn,parent_di,avs,xs,n),
       (ip,src,dst,ops,st,middle,last,limit_st),
       (next,d,p,srcaddr,sb,b,cap,oid,capacity),
       (ctx,fn,hdr,body_lbl,exit_lbl,hid,tail,prefix,bid,iv,nv)) /\
  entry_bytes_array_config cfg /\ entry_bytes_array_state cfg prepared j s /\
  j < LENGTH xs /\
  entry_loop_child_end fn tail prefix bid iv (STRING #"%" (toString nv))
    ip hdr src p srcaddr (LENGTH xs) j u /\
  entry_bytes_array_inv next limit_st d (type_memory_bytes ce (ArrayT ty (Dynamic maxn)))
    (w2n p) (LENGTH xs) prepared u /\ entry_loop_prefix tv xs d (SUC j) u /\
  entry_loop_fields s u /\ u.vs_allocas = s.vs_allocas /\
  u.vs_alloca_next = s.vs_alloca_next /\
  (!op w. abi_decoder_operand_live next op /\ eval_operand op s = SOME w ==>
     eval_operand op u = SOME w) ==>
  ?v. entry_bytes_array_state cfg prepared (SUC j) v /\
    entry_loop_fields s v /\ abi_decode_sim ctx fn u v
Proof
  strip_tac >>
  `?v. abi_decode_loop_ready hdr ip src CALLDATALOAD p srcaddr (LENGTH xs) (SUC j) v /\
    entry_bytes_array_inv next limit_st d (type_memory_bytes ce (ArrayT ty (Dynamic maxn)))
      (w2n p) (LENGTH xs) prepared v /\ entry_loop_prefix tv xs d (SUC j) v /\
    entry_loop_fields u v /\ abi_decode_sim ctx fn u v /\
    v = jump_to hdr (mstore (w2n p) (n2w (SUC j))
      (update_var (STRING #"%" (toString nv)) (n2w (SUC j)) u))` by
    (qpat_x_assum `cfg = _` SUBST_ALL_TAC >>
     qpat_x_assum `entry_bytes_array_config _`
       (strip_assume_tac o PURE_REWRITE_RULE [entry_bytes_array_config_def]) >>
     `?hdr_bb. lookup_block hdr fn.fn_blocks = SOME hdr_bb /\
       phi_prefix_length hdr_bb.bb_instructions = 0` by
       fs[abi_decode_loop_cfg_def, abi_decode_header_insts_def, phi_prefix_length_def, mk_inst_def] >>
     `!k. k < SUC j ==> w2n p+32 <= d+32+k*type_memory_size tv \/
       d+32+k*type_memory_size tv+type_memory_size tv <= w2n p` by
       (rpt strip_tac >> first_x_assum (qspec_then `k` mp_tac) >> simp[]) >>
     irule entry_bytes_array_backedge >> simp[SF SFY_ss]) >>
  `entry_loop_fields s v /\ v.vs_allocas = s.vs_allocas /\
   v.vs_alloca_next = s.vs_alloca_next` by
    fs[entry_loop_fields_def, jump_to_def, mstore_def, update_var_def,
       write_memory_with_expansion_def] >>
  `!op w. abi_decoder_operand_live next op /\ eval_operand op s = SOME w ==>
     eval_operand op v = SOME w` by suspend "live" >>
  `SUC j <= LENGTH xs` by decide_tac >>
  drule_all entry_bytes_array_state_transfer >> strip_tac >>
  qexists_tac `v` >> asm_rewrite_tac[]
QED

Resume entry_bytes_array_config_backedge[live]:
  qpat_x_assum `cfg = _` SUBST_ALL_TAC >>
  qpat_x_assum `entry_bytes_array_config _`
    (strip_assume_tac o PURE_REWRITE_RULE [entry_bytes_array_config_def]) >>
  rpt strip_tac >>
  `abi_decoder_operand_live nv op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `next` >> simp[]) >>
  asm_simp_tac (srw_ss()) [eval_operand_mstore, abi_decoder_generated_update_operand]
QED

Finalise entry_bytes_array_config_backedge

Theorem entry_bytes_array_iteration[local]:
  cfg = ((ce,env,sf,ty,tv,maxn,parent_di,avs,xs,n),
       (ip,src,dst,ops,st,middle,last,limit_st),
       (next,d,p,srcaddr,sb,b,cap,oid,capacity),
       (ctx,fn,hdr,body_lbl,exit_lbl,hid,tail,prefix,bid,iv,nv)) /\
  entry_bytes_array_config cfg /\ entry_bytes_array_state cfg prepared j s /\
  j < LENGTH xs ==>
  ?v. entry_bytes_array_state cfg prepared (SUC j) v /\
    entry_loop_fields s v /\ abi_decode_sim ctx fn s v
Proof
  strip_tac >>
  qabbrev_tac `h = jump_to body_lbl (abi_decode_header_state (STRING #"%" (toString next))
    (STRING #"%" (toString (next+1))) (STRING #"%" (toString (next+2)))
    (STRING #"%" (toString (next+3))) j (LENGTH xs) s)` >>
  `h = jump_to body_lbl (abi_decode_header_state (STRING #"%" (toString next))
    (STRING #"%" (toString (next+1))) (STRING #"%" (toString (next+2)))
    (STRING #"%" (toString (next+3))) j (LENGTH xs) s)` by simp[Abbr `h`] >>
  drule_all entry_bytes_array_config_header >> strip_tac >>
  drule_all entry_bytes_array_config_child >> strip_tac >>
  drule_all entry_bytes_array_child_memory >> strip_tac >>
  drule_all entry_bytes_array_child_tail >> strip_tac >>
  qabbrev_tac `u = t with vs_inst_idx := LENGTH prefix` >>
  `entry_bytes_array_inv next limit_st d (type_memory_bytes ce (ArrayT ty (Dynamic maxn)))
     (w2n p) (LENGTH xs) prepared u /\ entry_loop_prefix tv xs d (SUC j) u /\
   entry_loop_fields s u /\ u.vs_allocas = s.vs_allocas /\
   u.vs_alloca_next = s.vs_alloca_next` by suspend "adjust" >>
  `!op w. abi_decoder_operand_live next op /\ eval_operand op s = SOME w ==>
     eval_operand op u = SOME w` by suspend "live" >>
  `entry_loop_child_end fn tail prefix bid iv (STRING #"%" (toString nv))
     ip hdr src p srcaddr (LENGTH xs) j u /\ abi_decode_sim ctx fn h u` by
    fs[Abbr `u`] >>
  drule_all entry_bytes_array_config_backedge >> strip_tac >>
  `abi_decode_sim ctx fn s u` by metis_tac[abi_decode_sim_trans] >>
  `abi_decode_sim ctx fn s v` by metis_tac[abi_decode_sim_trans] >>
  qexists_tac `v` >> asm_rewrite_tac[]
QED

Resume entry_bytes_array_iteration[adjust]:
  fs[Abbr `u`, Abbr `h`, entry_bytes_array_inv_def, entry_loop_prefix_def,
    entry_loop_fields_def, jump_to_def, abi_decode_header_state_def, update_var_def,
    eval_operand_def, lookup_var_def, fresh_vars_wrt_def, abi_decode_footprint_frame_def]
QED

Resume entry_bytes_array_iteration[live]:
  rpt strip_tac >>
  `abi_decoder_operand_live st.cs_next_var op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `next` >> simp[]) >>
  `eval_operand op h = SOME w` by metis_tac[] >>
  `eval_operand op t = SOME w` by metis_tac[] >>
  Cases_on `op` >> fs[Abbr `u`, eval_operand_def, lookup_var_def]
QED

Finalise entry_bytes_array_iteration

Theorem entry_bytes_array_iterations[local]:
  !remaining j s.
  LENGTH xs = j + remaining /\
  cfg = ((ce,env,sf,ty,tv,maxn,parent_di,avs,xs,n),
       (ip,src,dst,ops,st,middle,last,limit_st),
       (next,d,p,srcaddr,sb,b,cap,oid,capacity),
       (ctx,fn,hdr,body_lbl,exit_lbl,hid,tail,prefix,bid,iv,nv)) /\
  entry_bytes_array_config cfg /\ entry_bytes_array_state cfg prepared j s ==>
  ?v. entry_bytes_array_state cfg prepared (LENGTH xs) v /\
    entry_loop_fields s v /\ abi_decode_sim ctx fn s v
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (qexists_tac `s` >> gvs[entry_loop_fields_def, abi_decode_sim_refl]) >>
  `j < LENGTH xs` by decide_tac >>
  drule_all entry_bytes_array_iteration >> strip_tac >>
  first_x_assum (qspecl_then [`SUC j`,`v`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  goal_assum (drule_at Any) >>
  conj_tac >- fs[entry_loop_fields_def] >>
  metis_tac[abi_decode_sim_trans]
QED

Theorem entry_bytes_array_exit[local]:
  cfg = ((ce,env,sf,ty,tv,maxn,parent_di,avs,xs,n),
       (ip,src,dst,ops,st,middle,last,limit_st),
       (next,d,p,srcaddr,sb,b,cap,oid,capacity),
       (ctx,fn,hdr,body_lbl,exit_lbl,hid,tail,prefix,bid,iv,nv)) /\
  entry_bytes_array_config cfg /\ entry_bytes_array_state cfg prepared (LENGTH xs) s ==>
  ?t. ~t.vs_halted /\ t.vs_current_bb = exit_lbl /\ t.vs_inst_idx = 0 /\
    entry_bytes_array_inv next limit_st d (type_memory_bytes ce (ArrayT ty (Dynamic maxn)))
      (w2n p) (LENGTH xs) prepared t /\
    val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV xs)) d t.vs_memory /\
    entry_loop_fields s t /\ abi_decode_sim ctx fn s t
Proof
  strip_tac >> qpat_x_assum `cfg = _` SUBST_ALL_TAC >>
  qpat_x_assum `entry_bytes_array_config _`
    (strip_assume_tac o PURE_REWRITE_RULE [entry_bytes_array_config_def]) >>
  qpat_x_assum `entry_bytes_array_state _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [entry_bytes_array_state_def]) >>
  qabbrev_tac `t = jump_to exit_lbl (abi_decode_header_state (STRING #"%" (toString next))
    (STRING #"%" (toString (next+1))) (STRING #"%" (toString (next+2)))
    (STRING #"%" (toString (next+3))) (LENGTH xs) (LENGTH xs) s)` >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  `abi_decode_sim ctx fn s t` by
    (drule_all abi_decode_ready_header_sim >> simp[Abbr `t`]) >>
  `entry_bytes_array_inv next limit_st d (type_memory_bytes ce (ArrayT ty (Dynamic maxn)))
      (w2n p) (LENGTH xs) prepared t` by
    (simp[Abbr `t`] >> irule entry_bytes_array_inv_header >> simp[]) >>
  `val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV xs)) d s.vs_memory` by
    (irule (cj 2 calldata_terminal_array_memory) >>
     fs[entry_loop_prefix_def, entry_bytes_array_inv_def]) >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  fs[Abbr `t`, abi_decode_loop_ready_def, entry_loop_fields_def,
    abi_decode_header_state_def, jump_to_def, update_var_def]
QED

Theorem entry_bytes_array_from_header[local]:
  cfg = ((ce,env,sf,ty,tv,maxn,parent_di,avs,xs,n),
       (ip,src,dst,ops,st,middle,last,limit_st),
       (next,d,p,srcaddr,sb,b,cap,oid,capacity),
       (ctx,fn,hdr,body_lbl,exit_lbl,hid,tail,prefix,bid,iv,nv)) /\
  entry_bytes_array_config cfg /\ entry_bytes_array_state cfg prepared 0 s ==>
  ?t. ~t.vs_halted /\ t.vs_current_bb = exit_lbl /\ t.vs_inst_idx = 0 /\
    entry_bytes_array_inv next limit_st d (type_memory_bytes ce (ArrayT ty (Dynamic maxn)))
      (w2n p) (LENGTH xs) prepared t /\
    val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV xs)) d t.vs_memory /\
    entry_loop_fields s t /\ abi_decode_sim ctx fn s t
Proof
  strip_tac >>
  `?v. entry_bytes_array_state cfg prepared (LENGTH xs) v /\
     entry_loop_fields s v /\ abi_decode_sim ctx fn s v` by
    (irule entry_bytes_array_iterations >>
     simp[SF SFY_ss] >> qexistsl_tac [`0`, `LENGTH xs`] >> gvs[]) >>
  drule_all entry_bytes_array_exit >> strip_tac >>
  goal_assum (drule_at Any) >> asm_rewrite_tac[] >>
  conj_tac >- fs[entry_loop_fields_def] >>
  metis_tac[abi_decode_sim_trans]
QED

Theorem entry_bytes_array_initialized_state[local]:
  cfg = ((ce,env,sf,ty,tv,maxn,parent_di,avs,xs,n),
       (ip,src,dst,ops,st,middle,last,limit_st),
       (next,d,p,srcaddr,sb,b,cap,oid,capacity),
       (ctx,fn,hdr,body_lbl,exit_lbl,hid,tail,prefix,bid,iv,nv)) /\
  fresh_vars_wrt limit_st prepared /\ ~prepared.vs_halted /\
  mem_word_at d prepared.vs_memory = n2w (LENGTH xs) /\
  eval_operand ip prepared = SOME p /\ eval_operand src prepared = SOME srcaddr /\
  mload (w2n p) prepared = 0w /\
  abi_decode_load CALLDATALOAD srcaddr prepared = n2w (LENGTH xs) /\
  alloca_inv prepared /\ FLOOKUP prepared.vs_allocas oid = SOME (d,capacity) /\
  abi_decoder_ranges CALLDATALOAD (Lit 0w) (Lit 0w) src dst 0 sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap prepared /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    (abi_decode_source CALLDATALOAD prepared) =
    enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) ==>
  entry_bytes_array_state cfg prepared 0 (jump_to hdr prepared)
Proof
  strip_tac >> qpat_x_assum `cfg = _` SUBST_ALL_TAC >>
  simp_tac bool_ss [entry_bytes_array_state_def] >>
  `entry_bytes_array_inv next limit_st d
     (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) (w2n p) (LENGTH xs)
     prepared prepared` by (irule entry_bytes_array_inv_init >> simp[]) >>
  fs[entry_bytes_array_inv_def, entry_loop_prefix_def, abi_decode_loop_ready_def,
     jump_to_def, abi_decoder_ranges_def, eval_operand_def, lookup_var_def,
     abi_decode_load_def, abi_decode_source_def, fresh_vars_wrt_def,
     entry_loop_fields_def, abi_decode_footprint_frame_def,
     mload_def, alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Theorem entry_array_initializer_outputs[local]:
  abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w) (Lit 0w) maxn abi_sz st =
    (setup,loop_st) ==>
  EVERY (\i. ~is_terminator i.inst_opcode /\
    EVERY (\x. ?k. x = STRING #"%" (toString k) /\ k < loop_st.cs_next_var)
      i.inst_outputs) (emitted_insts st loop_st)
Proof
  simp[abi_decode_array_loop_init_def, abi_decode_dynarray_prefix_def,
       abiDecoderDynarrayPrefixTheory.abi_decode_dynarray_position_prefix_unbounded,
       compile_abi_dec_addr_def,
       abi_decode_count_guard_def, abi_decode_dynarray_end_guard_def,
       abi_decode_array_header_def, abi_decode_index_init_def,
       compile_alloc_buffer_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def] >>
  metis_tac[arithmeticTheory.LESS_ADD]
QED

Theorem entry_array_initializer_final_fresh:
  abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w) (Lit 0w) maxn abi_sz st =
    (setup,loop_st) /\
  run_inst_seq (emitted_insts st loop_st) s = OK t /\
  loop_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  fresh_vars_wrt limit_st t
Proof
  strip_tac >> drule entry_array_initializer_outputs >> strip_tac >>
  simp_tac bool_ss [fresh_vars_wrt_def] >> rpt strip_tac >>
  `lookup_var (STRING #"%" (toString n)) t =
   lookup_var (STRING #"%" (toString n)) s` by
    (irule ctorAbiActualAllocTheory.ctor_actual_sequence_var_frame >>
     goal_assum (drule_at Any) >> fs[EVERY_MEM] >> rpt strip_tac >>
     first_x_assum drule >> strip_tac >> simp[] >>
     qpat_x_assum `!x. MEM x i.inst_outputs ==> _` drule >>
     strip_tac >> gvs[] >> decide_tac) >>
  gvs[fresh_vars_wrt_def, lookup_var_def, FLOOKUP_DEF] >> metis_tac[]
QED


Definition entry_array_init_resources_def:
  entry_array_init_resources dst src maxn abi_sz
    (st,guard_st,header_st,loop_st,ip,cnt)
    (ctx,fn,site,d,sz,b,cap,p,initial) <=>
  abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w) (Lit 0w) maxn abi_sz st =
    ((ip,cnt),loop_st) /\
  abi_decode_dynarray_prefix src CALLDATALOAD (Lit 0w) maxn abi_sz st = ((),guard_st) /\
  abi_decode_array_header dst src CALLDATALOAD guard_st = (cnt,header_st) /\
  abi_decode_index_init header_st = (ip,loop_st) /\
  alloca_frontier_inv ctx fn site initial /\ unit_alloca_budget ctx < dimword (:256) /\
  (!i. MEM i (emitted_insts header_st loop_st) ==> MEM i (fn_insts fn)) /\
  ((FLOOKUP initial.vs_allocas header_st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
   (FLOOKUP initial.vs_allocas header_st.cs_next_id = SOME (p,32) /\
    p < dimword (:256) /\ p+32 <= initial.vs_alloca_next)) /\
  b <= p /\ p+32 <= b+cap /\ alloca_inv initial /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  32 <= sz /\ d+sz <= initial.vs_alloca_next
End

Theorem entry_array_init_canonical[local]:
  entry_array_init_resources dst src maxn abi_sz
    (st,guard_st,header_st,loop_st,ip,cnt) (ctx,fn,site,d,sz,b,cap,p,initial) /\
  abi_decoder_ranges CALLDATALOAD (Lit 0w) (Lit 0w) src dst 0 sb
    (LENGTH (enc (Array NONE aty) (ListV avs))) d sz b cap initial /\
  mem_bytes_at sb (LENGTH (enc (Array NONE aty) (ListV avs)))
    (abi_decode_source CALLDATALOAD initial) = enc (Array NONE aty) (ListV avs) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  maxn < dimword (:256) /\ LENGTH avs <= maxn /\
  fresh_vars_wrt limit_st initial /\ loop_st.cs_next_var <= limit_st.cs_next_var ==>
  ?t. run_inst_seq (emitted_insts st loop_st) initial = OK t /\
    eval_operand ip t = SOME (n2w p) /\ mload p t = 0w /\
    eval_operand cnt t = SOME (n2w (LENGTH avs)) /\
    mem_word_at d t.vs_memory = n2w (LENGTH avs) /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
    FLOOKUP t.vs_allocas header_st.cs_next_id = SOME (p,32) /\
    (!id. id <> header_st.cs_next_id ==> FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    fresh_vars_wrt limit_st t /\
    abi_decode_footprint_frame [(d,32);(p,32)] initial t /\
    entry_loop_fields initial t /\ t.vs_halted = initial.vs_halted /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==> eval_operand op t = eval_operand op initial) /\
    abi_decoder_ranges CALLDATALOAD (Lit 0w) (Lit 0w) src dst 0 sb
      (LENGTH (enc (Array NONE aty) (ListV avs))) d sz b cap t /\
    mem_bytes_at sb (LENGTH (enc (Array NONE aty) (ListV avs)))
      (abi_decode_source CALLDATALOAD t) = enc (Array NONE aty) (ListV avs)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `entry_array_init_resources _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [entry_array_init_resources_def]) >>
  qpat_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_ranges_def]) >>
  `d < dimword (:256)` by decide_tac >>
  SUBGOAL_THEN ``d+sz <= p \/ p+32 <= d`` assume_tac >- decide_tac >>
  `abi_decode_load CALLDATALOAD (n2w sb : 256 word) initial = n2w (LENGTH avs)` by
    (irule abiCanonicalHeadSizeTheory.canonical_dynamic_array_count_load >>
     qexists_tac `aty` >> asm_rewrite_tac[]) >>
  drule_all entry_array_init_accepted_live >> strip_tac >>
  drule_all entry_array_initializer_final_fresh >> strip_tac >>
  qpat_assum `abi_decode_footprint_frame _ _ _`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decode_footprint_frame_def]) >>
  qpat_x_assum `mem_bytes_at _ _ (abi_decode_source _ _) = _`
    (assume_tac o PURE_REWRITE_RULE [abi_decode_source_def]) >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  pure_rewrite_tac[entry_loop_fields_def, abi_decoder_ranges_def,
     abi_decode_source_def] >>
  asm_rewrite_tac[] >> metis_tac[]
QED

Definition entry_bytes_array_resources_def:
  entry_bytes_array_resources dst src maxn asz st
    (ctx,fn,site,d,sz,b,cap,p,oid,capacity,initial) <=>
  ?guard_st header_st loop_st ip cnt.
    entry_array_init_resources dst src maxn asz
      (st,guard_st,header_st,loop_st,ip,cnt)
      (ctx,fn,site,d,sz,b,cap,p,initial) /\
    FLOOKUP initial.vs_allocas oid = SOME (d,capacity) /\
    oid <> header_st.cs_next_id /\ sz <= capacity /\
    (d+sz <= p \/ p+32 <= d)
End

Theorem entry_bytes_array_resources_parent[local]:
  entry_bytes_array_resources dst src maxn asz st
    (ctx,fn,site,d,sz,b,cap,p,oid,capacity,initial) ==>
  FLOOKUP initial.vs_allocas oid = SOME (d,capacity) /\ sz <= capacity
Proof
  simp_tac bool_ss [entry_bytes_array_resources_def] >> metis_tac[]
QED

Theorem entry_bytes_array_compile_phases:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecDynArray (DecBytestring n) asz msz T maxn) start = ((),final) /\
  abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w) (Lit 0w) maxn asz start =
    ((ip,cnt),loop_st) ==>
  ?labels body_st ops middle last.
    abi_decode_loop_prefix ip src CALLDATALOAD (Lit 0w) loop_st = (labels,body_st) /\
    abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) (Lit 0w)
      (DecBytestring n) asz msz body_st = (ops,middle) /\
    compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) CALLDATALOAD (Lit 0w)
      (Lit 0w) (DecBytestring n) middle = ((),last) /\
    abi_decode_loop_suffix ip (FST ops) (FST labels) (SND (SND labels)) last =
      ((),final)
Proof
  strip_tac >> drule abi_decode_loop_array_trace >> simp[] >> strip_tac >>
  gvs[] >> drule abi_decode_dyn_loop_trace >> simp[]
QED

Theorem entry_bytes_array_initializer_to_header[local]:
  abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w) (Lit 0w) maxn asz st =
    (setup,loop_st) /\ fn_has_code st loop_st fn /\
  run_inst_seq (emitted_insts st loop_st) initial = OK prepared /\
  prepared.vs_halted = initial.vs_halted /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  lookup_block loop_st.cs_current_bb fn.fn_blocks = SOME
    <|bb_label := loop_st.cs_current_bb; bb_instructions :=
      loop_st.cs_current_insts ++ [mk_inst loop_st.cs_next_id JMP [Label hdr] []]|> /\
  lookup_block hdr fn.fn_blocks = SOME hdr_bb /\
  phi_prefix_length hdr_bb.bb_instructions = 0 ==>
  abi_decode_sim ctx fn initial (jump_to hdr prepared)
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_loop_init_shape >> strip_tac >>
  drule_all abi_encoder_run_sequence_reach >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `~t.vs_halted` by fs[] >>
  `abi_decode_sim ctx fn t (jump_to hdr t)` by
    (irule abi_decoder_loop_entry_sim >> simp[SF SFY_ss] >>
     qexistsl_tac [`<|bb_label := loop_st.cs_current_bb; bb_instructions :=
       loop_st.cs_current_insts ++ [mk_inst loop_st.cs_next_id JMP [Label hdr] []]|>`,
       `loop_st.cs_next_id`, `loop_st.cs_current_insts`] >> fs[]) >>
  `jump_to hdr t = jump_to hdr prepared` by gvs[jump_to_def] >>
  metis_tac[abi_decode_sim_trans]
QED

Theorem entry_bytes_array_spatial[local]:
  type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= capacity /\
  LENGTH xs <= maxn /\
  (d+type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= p \/ p+32 <= d) ==>
  (d+32 <= p \/ p+32 <= d) /\
  (!k. k < LENGTH xs ==>
    32+k*type_memory_size tv <= capacity /\
    d+32+k*type_memory_size tv+type_memory_size tv <=
      d+type_memory_bytes ce (ArrayT ty (Dynamic maxn)) /\
    (p+32 <= d+32+k*type_memory_size tv \/
     d+32+k*type_memory_size tv+type_memory_size tv <= p))
Proof
  `type_memory_bytes ce (ArrayT ty (Dynamic maxn)) =
    32+maxn*type_memory_bytes ce ty` by simp[Once type_memory_bytes_def] >>
  asm_rewrite_tac[] >> strip_tac >>
  gvs[] >> rpt strip_tac >>
  `k+1 <= maxn` by decide_tac >>
  `(k+1)*type_memory_size tv <= maxn*type_memory_size tv` by simp[LE_MULT_RCANCEL] >>
  qpat_x_assum `(k+1)*_ <= maxn*_` mp_tac >>
  pure_rewrite_tac[RIGHT_ADD_DISTRIB, MULT_CLAUSES] >> decide_tac
QED

Theorem entry_bytes_array_code_split:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecDynArray (DecBytestring n) asz msz T maxn) st = ((),final) /\
  abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w) (Lit 0w) maxn asz st =
    ((ip,cnt),loop_st) /\ fn_has_code st final fn ==>
  fn_has_code st loop_st fn /\ fn_has_code loop_st final fn
Proof
  strip_tac >> drule abi_decode_loop_array_trace >> simp[] >> strip_tac >> gvs[] >>
  `cs_extends loop_st final` by
    (drule (PURE_REWRITE_RULE [cs_appends_def] (cj 3 cs_appends_abi_decode_mutual)) >> simp[]) >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_loop_init_shape >> strip_tac >>
  `cs_extends st loop_st` by (irule cs_extends_same_block >> simp[]) >>
  drule_all fn_has_code_split >> simp[]
QED

Theorem entry_bytes_array_phase_layout:
  abi_decode_loop_prefix ip src CALLDATALOAD (Lit 0w) loop_st = (labels,body_st) /\
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecBytestring n) asz msz body_st = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) CALLDATALOAD (Lit 0w)
    (Lit 0w) (DecBytestring n) middle = ((),last) /\
  abi_decode_loop_suffix ip (FST ops) (FST labels) (SND (SND labels)) last =
    ((),final) /\ fn_has_code loop_st final fn /\
  (!bb. lookup_block final.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  final.cs_next_var <= limit_st.cs_next_var ==>
  body_st.cs_current_bb = FST (SND labels) /\ body_st.cs_current_insts = [] /\
  fn_has_code body_st last fn /\
  abi_decode_loop_cfg fn (FST labels) (FST (SND labels)) (SND (SND labels))
    (loop_st.cs_next_id+1) ip src CALLDATALOAD
    (STRING #"%" (toString loop_st.cs_next_var))
    (STRING #"%" (toString (loop_st.cs_next_var+1)))
    (STRING #"%" (toString (loop_st.cs_next_var+2)))
    (STRING #"%" (toString (loop_st.cs_next_var+3))) /\
  (?bb. lookup_block last.cs_current_bb fn.fn_blocks = SOME bb /\
    bb.bb_instructions = last.cs_current_insts ++
      abi_decode_backedge_insts last.cs_next_id
        (STRING #"%" (toString body_st.cs_next_var))
        (STRING #"%" (toString last.cs_next_var)) ip (FST labels)) /\
  FST ops = Var (STRING #"%" (toString body_st.cs_next_var)) /\
  loop_st.cs_next_var <= body_st.cs_next_var /\
  loop_st.cs_next_var+4 <= limit_st.cs_next_var /\
  middle.cs_next_var <= limit_st.cs_next_var /\
  last.cs_next_var < limit_st.cs_next_var /\
  loop_st.cs_next_var <= last.cs_next_var /\
  final.cs_current_bb = SND (SND labels) /\ final.cs_current_insts = []
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_loop_phase_cfg >> strip_tac >>
  drule_all abi_decoder_loop_phase_lookups >> strip_tac >>
  drule_all abi_decoder_loop_phase_containment >> strip_tac >>
  drule abi_decoder_loop_prefix_facts >> strip_tac >>
  drule abi_decoder_array_setup_head >> strip_tac >>
  `abi_decode_loop_suffix ip (Var (STRING #"%" (toString body_st.cs_next_var)))
     (FST labels) (SND (SND labels)) last = ((),final)` by metis_tac[] >>
  drule abi_decoder_loop_suffix_facts >> strip_tac >>
  drule_all abi_decoder_array_body_code >> strip_tac >>
  gvs[] >> simp[SF SFY_ss]
QED

Theorem entry_bytes_array_concrete_config:
  abi_decode_loop_prefix ip src CALLDATALOAD (Lit 0w) loop_st = (labels,body_st) /\
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecBytestring n) (abi_embedded_static_size ce.ce_struct_fields ty)
    (type_memory_bytes ce ty) body_st = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) CALLDATALOAD (Lit 0w)
    (Lit 0w) (DecBytestring n) middle = ((),last) /\
  abi_decode_loop_suffix ip (FST ops) (FST labels) (SND (SND labels)) last =
    ((),final) /\ fn_has_code loop_st final fn /\
  (!bb. lookup_block final.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  final.cs_next_var <= limit_st.cs_next_var /\
  type_to_abi_dec_info sf ce ty = DecBytestring n /\ n < dimword (:256) /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV avs) (ArrayV (DynArrayV xs)) /\
  is_dynamic (vyper_to_abi_type env ty) /\
  type_memory_bytes ce ty = type_memory_size tv /\ EVERY (val_wf tv) xs /\
  LENGTH xs <= maxn /\ maxn < dimword (:256) /\
  abi_decoder_operand_live loop_st.cs_next_var ip /\
  abi_decoder_operand_live loop_st.cs_next_var src /\
  abi_decoder_operand_live loop_st.cs_next_var dst /\
  type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= capacity /\
  (d+type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= w2n p \/ w2n p+32 <= d) ==>
  entry_bytes_array_config
    ((ce,env,sf,ty,tv,maxn,parent_di,avs,xs,n),
     (ip,src,dst,ops,body_st,middle,last,limit_st),
     (loop_st.cs_next_var,d,p,srcaddr,sb,b,cap,oid,capacity),
     (ctx,fn,FST labels,FST (SND labels),SND (SND labels),loop_st.cs_next_id+1,
      last.cs_current_bb,last.cs_current_insts,last.cs_next_id,
      STRING #"%" (toString body_st.cs_next_var),last.cs_next_var))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all entry_bytes_array_phase_layout >> strip_tac >>
  drule_all entry_bytes_array_spatial >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `src <> Var (STRING #"%" (toString loop_st.cs_next_var))` by
    (irule abi_decoder_live_excludes_output >> qexists_tac `loop_st.cs_next_var` >> simp[]) >>
  pure_rewrite_tac[entry_bytes_array_config_def] >>
  asm_rewrite_tac[] >> simp[] >> metis_tac[]
QED

Theorem entry_bytes_array_initial_live:
  abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w) (Lit 0w) maxn asz st =
    ((ip,cnt),loop_st) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst ==>
  abi_decoder_operand_live loop_st.cs_next_var ip /\
  abi_decoder_operand_live loop_st.cs_next_var src /\
  abi_decoder_operand_live loop_st.cs_next_var dst
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_loop_init_shape >> strip_tac >>
  drule abi_decode_array_loop_init_trace >> strip_tac >> gvs[] >>
  drule abi_decode_index_init_shape >> strip_tac >>
  conj_tac >-
    (gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def] >> decide_tac) >>
  conj_tac >> irule abi_decoder_operand_live_mono >>
  qexists_tac `st.cs_next_var` >> simp[]
QED

Theorem entry_bytes_array_compiled_config[local]:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecDynArray (DecBytestring n) (abi_embedded_static_size ce.ce_struct_fields ty)
      (type_memory_bytes ce ty) T maxn) st = ((),final) /\
  fn_has_code st final fn /\
  (!bb. lookup_block final.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  entry_bytes_array_resources dst src maxn (abi_embedded_static_size ce.ce_struct_fields ty) st
    (ctx,fn,site,d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)),b,cap,p,oid,capacity,initial) /\
  type_to_abi_dec_info sf ce ty = DecBytestring n /\ n < dimword (:256) /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV avs) (ArrayV (DynArrayV xs)) /\
  is_dynamic (vyper_to_abi_type env ty) /\
  type_memory_bytes ce ty = type_memory_size tv /\ EVERY (val_wf tv) xs /\
  LENGTH xs <= maxn /\ maxn < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  final.cs_next_var <= limit_st.cs_next_var /\ p < dimword (:256) ==>
  ?guard_st header_st loop_st ip cnt labels body_st ops middle last.
    entry_array_init_resources dst src maxn (abi_embedded_static_size ce.ce_struct_fields ty)
      (st,guard_st,header_st,loop_st,ip,cnt)
      (ctx,fn,site,d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)),b,cap,p,initial) /\
    oid <> header_st.cs_next_id /\ FLOOKUP initial.vs_allocas oid = SOME (d,capacity) /\
    fn_has_code st loop_st fn /\ loop_st.cs_next_var <= limit_st.cs_next_var /\
    entry_bytes_array_config
      ((ce,env,sf,ty,tv,maxn,parent_di,avs,xs,n),
       (ip,src,dst,ops,body_st,middle,last,limit_st),
       (loop_st.cs_next_var,d,(n2w p:bytes32),(srcaddr:bytes32),(sb:num),b,cap,oid,capacity),
       (ctx,fn,FST labels,FST (SND labels),SND (SND labels),loop_st.cs_next_id+1,
        last.cs_current_bb,last.cs_current_insts,last.cs_next_id,
        STRING #"%" (toString body_st.cs_next_var),last.cs_next_var)) /\
    lookup_block loop_st.cs_current_bb fn.fn_blocks = SOME
      <|bb_label := loop_st.cs_current_bb; bb_instructions := loop_st.cs_current_insts ++
        [mk_inst loop_st.cs_next_id JMP [Label (FST labels)] []]|> /\
    (?hdr_bb. lookup_block (FST labels) fn.fn_blocks = SOME hdr_bb /\
      phi_prefix_length hdr_bb.bb_instructions = 0) /\
    final.cs_current_bb = SND (SND labels) /\ final.cs_current_insts = []
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `entry_bytes_array_resources _ _ _ _ _ _`
    (CHOOSE_THEN (CHOOSE_THEN (CHOOSE_THEN (CHOOSE_THEN
      (CHOOSE_THEN (map_every assume_tac o CONJUNCTS))))) o
      PURE_REWRITE_RULE [entry_bytes_array_resources_def]) >>
  qpat_assum `entry_array_init_resources _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [entry_array_init_resources_def]) >>
  drule_all entry_bytes_array_code_split >> strip_tac >>
  drule_all entry_bytes_array_compile_phases >> strip_tac >>
  drule_all entry_bytes_array_initial_live >> strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all entry_bytes_array_phase_layout >> strip_tac >>
  `loop_st.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all abi_decoder_loop_phase_entry >> strip_tac >>
  drule_all abi_decoder_loop_phase_lookups >> strip_tac >>
  qexistsl_tac [`guard_st`,`header_st`,`loop_st`,`ip`,`cnt`,`labels`,`body_st`,`ops`,`middle`,`last`] >>
  asm_rewrite_tac[] >> conj_tac
  >- (irule entry_bytes_array_concrete_config >> simp[SF SFY_ss]) >>
  simp[abi_decode_header_insts_def, phi_prefix_length_def, mk_inst_def, SF SFY_ss]
QED

Theorem entry_bytes_array_pointer_bound[local]:
  entry_bytes_array_resources dst src maxn asz st
    (ctx,fn,site,d,sz,b,cap,p,oid,capacity,initial) ==> p < dimword (:256)
Proof
  simp_tac bool_ss [entry_bytes_array_resources_def, entry_array_init_resources_def] >>
  strip_tac >>
  qpat_x_assum `alloca_frontier_inv _ _ _ _` mp_tac >>
  simp_tac bool_ss [alloca_frontier_inv_def] >> strip_tac >> gvs[] >> decide_tac
QED

Theorem entry_canonical_bytes_array_execution:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecDynArray (DecBytestring n) (abi_embedded_static_size ce.ce_struct_fields ty)
      (type_memory_bytes ce ty) T maxn) st = ((),final) /\
  fn_has_code st final fn /\
  (!bb. lookup_block final.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    (DecDynArray (DecBytestring n) (abi_embedded_static_size ce.ce_struct_fields ty)
      (type_memory_bytes ce ty) T maxn) (ListV avs) (ArrayV (DynArrayV xs)) /\
  type_to_abi_dec_info sf ce ty = DecBytestring n /\
  is_dynamic (vyper_to_abi_type env ty) /\
  type_memory_bytes ce ty = type_memory_size tv /\ EVERY (val_wf tv) xs /\
  LENGTH xs = LENGTH avs /\ LENGTH xs <= maxn /\
  maxn < dimword (:256) /\ n < dimword (:256) /\
  entry_bytes_array_resources dst src maxn (abi_embedded_static_size ce.ce_struct_fields ty) st
    (ctx,fn,site,d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)),b,cap,p,oid,capacity,initial) /\
  abi_decoder_ranges CALLDATALOAD (Lit 0w) (Lit 0w) src dst 0 sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    (abi_decode_source CALLDATALOAD initial) =
    enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  fresh_vars_wrt limit_st initial /\ final.cs_next_var <= limit_st.cs_next_var /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV xs)) d t.vs_memory /\
    ~t.vs_halted /\ t.vs_current_bb = final.cs_current_bb /\
    t.vs_inst_idx = LENGTH final.cs_current_insts /\ fresh_vars_wrt limit_st t /\
    entry_loop_fields initial t /\
    abi_decode_footprint_frame [(d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)));(p,32)] initial t /\
    abi_decode_sim ctx fn initial t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule entry_bytes_array_pointer_bound >> strip_tac >>
  drule_all entry_bytes_array_compiled_config >>
  disch_then (qspecl_then [`n2w sb`,`sb`] strip_assume_tac) >>
  `has_type (Array NONE (vyper_to_abi_type env ty)) (ListV avs)` by
    (qpat_assum `abi_decoder_metadata _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_decoder_metadata_def, vyperABITheory.vyper_to_abi_type_def] >>
     metis_tac[]) >>
  `LENGTH avs <= maxn` by decide_tac >>
  qmatch_asmsub_abbrev_tac `entry_bytes_array_config cfg` >>
  drule_all entry_array_init_canonical >> strip_tac >>
  qpat_x_assum `compile_abi_decode_to_buf dst src _ (Lit 0w) _ _ st = _` kall_tac >>
  qpat_x_assum `abi_decoder_metadata _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `abi_decoder_coherent _ _ _ _ _` kall_tac >>
  `FLOOKUP t.vs_allocas oid = SOME (d,capacity)` by metis_tac[] >>
  `eval_operand src t = SOME (n2w sb)` by
    (qpat_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _ _ t` mp_tac >>
     pure_rewrite_tac[abi_decoder_ranges_def] >> metis_tac[]) >>
  `abi_decode_load CALLDATALOAD (n2w sb:bytes32) t = n2w (LENGTH xs)` by
    (asm_rewrite_tac[] >> irule abiCanonicalHeadSizeTheory.canonical_dynamic_array_count_load >>
     qexists_tac `vyper_to_abi_type env ty` >> asm_rewrite_tac[] >>
     qpat_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _ _ t` mp_tac >>
     pure_rewrite_tac[abi_decoder_ranges_def] >> metis_tac[]) >>
  `w2n (n2w p:bytes32) = p` by simp[] >>
  `entry_bytes_array_state cfg t 0 (jump_to (FST labels) t)` by
    (irule entry_bytes_array_initialized_state >>
     simp_tac bool_ss [Abbr `cfg`] >> asm_rewrite_tac[] >> metis_tac[]) >>
  `abi_decode_sim ctx fn initial (jump_to (FST labels) t)` by suspend "initial_sim" >>
  qpat_assum `Abbrev (cfg = _)` (assume_tac o PURE_REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_all entry_bytes_array_from_header >> strip_tac >>
  qexists_tac `t'` >> asm_rewrite_tac[] >> suspend "final_frames"
QED

Resume entry_canonical_bytes_array_execution[initial_sim]:
  qpat_assum `entry_array_init_resources _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [entry_array_init_resources_def]) >>
  irule entry_bytes_array_initializer_to_header >> simp_tac bool_ss [] >>
  asm_rewrite_tac[] >> simp[SF SFY_ss] >>
  goal_assum (drule_at Any) >> simp[SF SFY_ss]
QED

Resume entry_canonical_bytes_array_execution[final_frames]:
  qpat_assum `entry_bytes_array_inv _ _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [entry_bytes_array_inv_def]) >>
  `32 <= type_memory_bytes ce (ArrayT ty (Dynamic maxn))` by
    simp[Once type_memory_bytes_def] >>
  `abi_decode_footprint_frame
    [(d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)));(p,32)] initial t` by
    (irule abi_decode_footprint_frame_weaken >>
     qexists_tac `[(d,32);(p,32)]` >> asm_rewrite_tac[] >>
     qpat_assum `32 <= type_memory_bytes ce (ArrayT ty (Dynamic maxn))` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp_tac bool_ss [MEM] >> rpt strip_tac >>
     gvs[] >> simp[LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM]) >>
  simp_tac bool_ss [listTheory.LENGTH, GSYM CONJ_ASSOC] >>
  conj_tac >- asm_rewrite_tac[] >>
  conj_tac >-
    (qpat_assum `entry_loop_fields initial t` mp_tac >>
     qpat_assum `entry_loop_fields t t'` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[entry_loop_fields_def] >> metis_tac[]) >>
  conj_tac >-
    (qpat_assum `abi_decode_footprint_frame _ t t'` mp_tac >>
     qpat_assum `abi_decode_footprint_frame [(d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)));(p,32)] initial t` mp_tac >>
     qpat_assum `w2n (n2w p:bytes32) = p` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[abi_decode_footprint_frame_trans]) >>
  qpat_assum `abi_decode_sim ctx fn initial _` mp_tac >>
  qpat_assum `abi_decode_sim ctx fn _ t'` mp_tac >>
  rpt (pop_assum kall_tac) >> metis_tac[abi_decode_sim_trans]
QED

Finalise entry_canonical_bytes_array_execution
