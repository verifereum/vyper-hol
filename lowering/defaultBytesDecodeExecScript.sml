(* Exact successful arbitrary-calldata bytes decoder execution. *)
Theory defaultBytesDecodeExec
Ancestors abiEncoder abiDecoderGuards emitHelper exprLowering calldataSourceCorrespondence calldataExact calldataBytesLive calldataBytesLeaf calldataSourceWord
  abiDecoderBytestringOutcome abiDecoderBytesPhases abiDecoderCoherence
  abiDecoderContract abiDecoderClamp exprLoweringProps fragExecMem
  vyperValue vyperCalldata valueEncodingTyping venomState venomExecSemantics
  compileEnv words list rich_list arithmetic venomInst

Theorem calldata_copy_step_static[local]:
  inst.inst_opcode = CALLDATACOPY /\ step_inst_base inst s = OK t ==>
  t = s with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory|>
Proof
  strip_tac >> qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  PURE_ONCE_REWRITE_TAC [step_inst_base_def] >>
  asm_rewrite_tac [opcode_case_def] >>
  simp[AllCaseEqs()] >> rpt strip_tac >>
  gvs[write_memory_with_expansion_def] >>
  simp[venom_state_component_equality]
QED

Theorem calldata_bytes_sequence_static[local]:
  !insts s t.
  EVERY (\i. abi_bytes_opcode i.inst_opcode \/ i.inst_opcode = CALLDATACOPY) insts /\
  run_inst_seq insts s = OK t ==>
  t = s with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory|>
Proof
  Induct >> simp[run_inst_seq_def] >> rpt strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  rename1 `step_inst_base h s = OK u` >>
  `u = s with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory|>` by
    metis_tac[abi_bytes_step_static, calldata_copy_step_static] >>
  first_x_assum drule_all >> strip_tac >>
  fs[venom_state_component_equality]
QED

Theorem default_bytes_decode_exact_sequence:
  abi_decoder_coherent ce env sf ty tv /\ is_bytestring_type ty /\
  compile_abi_decode_to_buf (Var dstvar) src CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce ty) sa = ((),sb) /\
  cd_decode F s.vs_call_ctx.cc_calldata tv (w2n sw) = SOME x /\
  eval_operand src s = SOME sw /\ eval_operand (Var dstvar) s = SOME (n2w d) /\
  abi_decoder_operand_live sa.cs_next_var src /\
  abi_decoder_operand_live sa.cs_next_var (Var dstvar) /\
  d+type_memory_size tv <= s.vs_alloca_next /\
  d+type_memory_size tv < dimword (:256) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    run_inst_seq_mem_ok (emitted_insts sa sb) s /\
    val_in_memory tv x d t.vs_memory /\ value_has_type tv x /\ val_wf tv x /\
    abi_decode_frame d (type_memory_size tv) s t /\
    (!op. abi_decoder_operand_live sa.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t = s with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory|> /\
    inst_extends sa sb /\ sb.cs_current_bb = sa.cs_current_bb /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
      ~is_terminator i.inst_opcode /\ i.inst_opcode <> ALLOCA)
      (emitted_insts sa sb)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule abi_decoder_coherent_header >>
  simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >>
  `?maxn. type_to_abi_dec_info sf ce ty = DecBytestring maxn /\
    type_memory_size tv = abi_decode_bytes_copy_size maxn /\
    MEM tv [BaseTV (BytesT (Dynamic maxn)); BaseTV (StringT maxn)]` by
    (qpat_x_assum `evaluate_type env ty = SOME tv` mp_tac >>
     qpat_x_assum `is_bytestring_type ty` mp_tac >>
     rpt (pop_assum kall_tac) >>
     Cases_on `ty` >> simp[is_bytestring_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> simp[is_bytestring_type_def] >>
     rpt strip_tac >> gvs[vyperValueTheory.evaluate_type_def, is_bytestring_type_def, AllCaseEqs()] >>
     simp[type_to_abi_dec_info_def, type_memory_bytes_def,
       valueEncodingTheory.type_memory_size_def, vfmConstantsTheory.word_size_def,
       abiDecoderBytesTheory.abi_decode_bytes_copy_size_def]) >>
  `maxn < dimword (:256)` by
    (irule abi_decode_bytes_extent_capacity_bound >> qexists `d` >> simp[]) >>
  `w2n (abi_decode_load CALLDATALOAD sw s) <= maxn` by
    (qpat_x_assum `cd_decode F _ _ _ = SOME x` mp_tac >>
     qpat_assum `MEM tv _` mp_tac >> simp_tac list_ss [MEM] >>
     strip_tac >> simp[cd_decode_def, GSYM calldata_decode_load_word, AllCaseEqs()] >>
     rpt strip_tac >> gvs[]) >>
  `compile_abi_decode_to_buf (Var dstvar) src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecBytestring maxn) sa = ((),sb)` by metis_tac[] >>
  `d+abi_decode_bytes_copy_size maxn < dimword (:256) /\
    d+abi_decode_bytes_copy_size maxn <= s.vs_alloca_next` by metis_tac[] >>
  drule_all calldata_bytes_accepted_live >> strip_tac >>
  `value_has_type tv x /\ val_wf tv x /\ val_in_memory tv x d t.vs_memory` by
    (qpat_assum `MEM tv _` mp_tac >> simp_tac list_ss [MEM] >>
     disch_tac >> fs[calldata_decode_load_word] >>
     drule_at (Pos (el 3)) calldata_exact_bytestring_reconstruction >>
     disch_then (qspec_then `tv` mp_tac) >> simp[] >> metis_tac[]) >>
  mp_tac (calldata_bytes_prefix_live |> Q.INST
    [`dst` |-> `Var dstvar`, `p` |-> `sw`, `st` |-> `sa`, `st'` |-> `sb`]) >>
  (impl_tac >- simp[]) >> disch_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule run_inst_seq_mem_ok_of_prefix_safe >> simp[] >>
     drule calldata_bytes_opcodes >> gvs[EVERY_MEM] >> metis_tac[]) >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_bytes_position_shape >> strip_tac >>
  qexists `t` >> simp[] >>
  conj_tac >- metis_tac[] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ (DecBytestring _) _ = _` mp_tac >>
  simp[compile_abi_decode_to_buf_def, compile_abi_dec_addr_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def,
    abi_decode_count_guard_def, emit_op_def, emit_void_def,
    fresh_var_def, fresh_id_def, emit_def] >> strip_tac >>
  gvs[emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  gvs[DROP_LENGTH_APPEND] >>
  (conj_tac >- (
    drule_at (Pos (el 2)) calldata_bytes_sequence_static >>
    (impl_tac >- (
      pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
      simp[DROP_LENGTH_APPEND, mk_inst_def, abi_bytes_opcode_def,
        abiDecoderWordOutcomeTheory.abi_word_opcode_def])) >>
    simp[]) >>
  simp[mk_inst_def, is_terminator_def])
QED
