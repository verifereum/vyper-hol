Theory ctorDeployMemoryRunMemEntryWord
Ancestors
  abiDecoderRange loweringStateRelDefs
  ctorDeployMemoryRunMemEntryCheckedStep ctorAbiActualLabelWord
  ctorAbiActualWordRun ctorAbiActualWorld abiDecoderPrimitiveCaller
  ctorAbiActualObservations ctorAbiActualNarrowWord allocaFrontierBound allocaBudgetProps
  abiEncoderRegisteredEffect abiDecoderWordTyped abiDecoderLayout abiDecoderTypedContract
  abiDecoderCoherence valueEncoding instIdxIndep venomMemDefs
  entryHaltMem fragGasSeqMem fragGasPathMem fragExec rich_list allocaHistory
  abiDecoderClampedWord abiDecoderContract abiDecoderClamp
  instMemFrontier memSafeRun words list arithmetic venomInstProofs venomExecSemantics
  emitHelperProps fragExecMem venomInst abiDecoderGuards abiDecoderReservation
  abiEncoder compileEnv exprLoweringProps venomState
  ctorDeployMemoryRunMemEntryReentry abiDecoderReentry abiDecoderReentryPointer

Theorem ctor_word_load_mem_ok:
  emit_op DLOAD [src] st = (v,st') /\
  eval_operand src s = SOME (n2w sb) /\ sb < dimword (:256) /\
  sb + 32 <= LENGTH s.vs_data_section ==>
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  simp[run_inst_seq_mem_ok_last] >> conj_tac
  >- (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  simp[inst_dload_in_section_def, mk_inst_def] >> rpt strip_tac >>
  gvs[w2n_n2w]
QED

Theorem ctor_word_store_mem_ok:
  emit_void MSTORE [dst;value] st = ((),st') /\
  eval_operand dst s = SOME (n2w d) /\ d < dimword (:256) /\
  d + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  simp[run_inst_seq_mem_ok_last, below_frontier_MSTORE, w2n_n2w]
QED

Theorem ctor_word_fresh_mem_ok:
  compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi (DecPrimWord clamp) st = ((),st') /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  sb < dimword (:256) /\ d < dimword (:256) /\
  sb + 32 <= LENGTH s.vs_data_section /\ d + 32 <= s.vs_alloca_next /\
  abi_decoder_clamp_valid clamp (abi_decode_load DLOAD (n2w sb : bytes32) s) /\
  fresh_vars_wrt st s ==>
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  simp_tac bool_ss [compile_abi_decode_to_buf_def, compile_abi_dec_addr_def, comp_return_def, compile_abi_decode_range_check_def, compile_abi_decode_static_def,
    comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op DLOAD [src] st = (val_op,c1)` >>
  pairarg_tac >> gvs[] >>
  rename1 `compile_abi_clamp_basetype val_op clamp c1 = ((),c2)` >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_read >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  drule abi_decoder_clamp_sequence >>
  disch_then (qspecl_then [`abi_decode_load DLOAD (n2w sb : bytes32) s`, `s1`] mp_tac) >>
  asm_simp_tac bool_ss [] >> rewrite_tac[] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  `run_inst_seq (emitted_insts st c2) s = OK s2 /\ inst_extends st c2` by
    (irule abi_decode_sequence_chain >> qexistsl [`s1`, `c1`] >> simp[]) >>
  `s2.vs_alloca_next = s1.vs_alloca_next` by
    (drule_all abi_decoder_clamp_shape >> strip_tac >>
     `EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
        (emitted_insts c1 c2)` by fs[EVERY_CONJ] >>
     drule_all abi_decode_sequence_allocation_frame >> simp[]) >>
  `s1.vs_alloca_next = s.vs_alloca_next` by
    (drule emitted_insts_emit_op >> strip_tac >>
     `step_inst_base (mk_inst st.cs_next_id DLOAD [src]
       [STRING #"%" (toString st.cs_next_var)]) s =
       OK (update_var (STRING #"%" (toString st.cs_next_var))
         (abi_decode_load DLOAD (n2w sb : bytes32) s) s)` by
       (irule abi_decode_read_step >> simp[]) >>
     gvs[run_inst_seq_def, update_var_def]) >>
  `emitted_insts st st' = emitted_insts st c2 ++ emitted_insts c2 st'` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `run_inst_seq_mem_ok (emitted_insts st c1) s` by
    (irule ctor_word_load_mem_ok >> metis_tac[]) >>
  `!u. run_inst_seq_mem_ok (emitted_insts c1 c2) u` by
    (gen_tac >> irule compile_abi_clamp_basetype_mem_ok >> metis_tac[]) >>
  `emitted_insts st c2 = emitted_insts st c1 ++ emitted_insts c1 c2` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `run_inst_seq_mem_ok (emitted_insts st c2) s` by
    (once_asm_rewrite_tac[] >> irule run_inst_seq_mem_ok_append >> simp[]) >>
  once_asm_rewrite_tac[] >> irule run_inst_seq_mem_ok_append >>
  simp[] >> rpt strip_tac >> gvs[] >>
  irule ctor_word_store_mem_ok >> metis_tac[]
QED

Theorem ctor_word_reentry_mem_ok:
  compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi (DecPrimWord clamp) st = ((),st') /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  sb < dimword (:256) /\ d < dimword (:256) /\
  sb + 32 <= LENGTH initial.vs_data_section /\ d + 32 <= initial.vs_alloca_next /\
  abi_decoder_clamp_valid clamp (abi_decode_load DLOAD (n2w sb : bytes32) initial) ==>
  run_inst_seq_mem_ok (emitted_insts st st') initial
Proof
  strip_tac >>
  qabbrev_tac `pruned = abi_decoder_prune_vars st.cs_next_var initial` >>
  `eval_operand src pruned = SOME (n2w sb) /\
   eval_operand dst pruned = SOME (n2w d) /\ fresh_vars_wrt st pruned /\
   sb + 32 <= LENGTH pruned.vs_data_section /\ d + 32 <= pruned.vs_alloca_next /\
   abi_decoder_clamp_valid clamp (abi_decode_load DLOAD (n2w sb : bytes32) pruned)` by
    (asm_simp_tac bool_ss [Abbr `pruned`, abi_decoder_prune_eval, abi_decoder_prune_fresh] >>
     gvs[abi_decoder_prune_vars_def, abi_decode_load_def, w2n_n2w, LESS_MOD]) >>
  `run_inst_seq_mem_ok (emitted_insts st st') pruned` by
    (irule ctor_word_fresh_mem_ok >> metis_tac[]) >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_word_reentry_code >> strip_tac >>
  `eval_operand (Lit 0w) pruned = SOME (n2w 0)` by simp[eval_operand_def] >>
  drule_all (SRULE [] (Q.INST [`B` |-> `0`] abi_decoder_clamped_word_sequence)) >> strip_tac >>
  irule ctor_reentry_sequence_mem >> conj_tac >- simp[] >>
  qexistsl [`initial.vs_vars`, `pruned`, `t`] >>
  simp[Abbr `pruned`, abi_decoder_prune_extension]
QED

Theorem ctor_word_sequence_path:
  compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi (DecPrimWord clamp) st = ((),st') /\
  fn_has_code st st' func /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts /\
  run_inst_seq_mem_ok (emitted_insts st st') s /\
  run_inst_seq (emitted_insts st st') s = OK t ==>
  gas_path_mem ctx func s
    (LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts st st')))
    (OK (t with vs_inst_idx := LENGTH st'.cs_current_insts))
Proof
  strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_clamped_word_shape >> strip_tac >>
  `?bb. lookup_block st.cs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX st'.cs_current_insts bb.bb_instructions` by
    (gvs[fn_has_code_def] >> metis_tac[]) >>
  `?code. st'.cs_current_insts = st.cs_current_insts ++ code /\
          emitted_insts st st' = code` by
    (qpat_x_assum `isPREFIX st.cs_current_insts st'.cs_current_insts` mp_tac >>
     simp[IS_PREFIX_APPEND] >> strip_tac >>
     simp[emitted_insts_def, DROP_LENGTH_APPEND]) >>
  `isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `isPREFIX st'.cs_current_insts _` mp_tac >>
     simp[IS_PREFIX_APPEND] >> strip_tac >>
     simp[IS_PREFIX_APPEND] >>
     rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code` by
    fs[EVERY_CONJ] >>
  `gas_path_mem ctx func s
     (LENGTH (FILTER (\i. i.inst_opcode = GAS) code))
     (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH code))` by
    (irule run_inst_seq_gas_path_mem >> gvs[] >> metis_tac[]) >>
  gvs[]
QED

Theorem ctor_word_sequence_zero_path:
  compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi (DecPrimWord clamp) st = ((),st') /\
  fn_has_code st st' func /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts /\
  run_inst_seq_mem_ok (emitted_insts st st') s /\
  run_inst_seq (emitted_insts st st') s = OK t ==>
  gas_path_mem ctx func s 0 (OK (t with vs_inst_idx := LENGTH st'.cs_current_insts)) /\
  t.vs_gas_readings = s.vs_gas_readings
Proof
  strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_word_reentry_code >> strip_tac >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts st st') = []` by
    (simp[FILTER_EQ_NIL, EVERY_MEM] >> rpt strip_tac >>
     fs[EVERY_MEM] >> first_x_assum drule >>
     simp[abiDecoderVarSequenceTheory.abi_decoder_reentry_opcode_def]) >>
  drule_all ctor_word_sequence_path >> disch_then (qspec_then `ctx` mp_tac) >>
  simp[] >> strip_tac >>
  drule gas_path_mem_ok_suffix >> simp[]
QED

Theorem ctor_sequence_history_advance:
  alloca_history func s /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
  EVERY (\i. i.inst_opcode <> ALLOCA) code /\
  t.vs_allocas = s.vs_allocas /\ t.vs_current_bb = s.vs_current_bb /\
  t.vs_inst_idx = s.vs_inst_idx + LENGTH code ==>
  alloca_history func t
Proof
  strip_tac >> fs[alloca_history_def] >> rpt strip_tac >>
  Cases_on `k < s.vs_inst_idx` >- metis_tac[] >>
  `k - s.vs_inst_idx < LENGTH code` by decide_tac >>
  `EL (k - s.vs_inst_idx) code = inst` by
    (fs[IS_PREFIX_APPEND, get_instruction_def] >>
     qpat_x_assum `DROP _ _ = _` (mp_tac o Q.AP_TERM `EL (k - s.vs_inst_idx)`) >>
     simp[EL_APPEND1, EL_DROP]) >>
  fs[EVERY_MEM] >>
  `MEM inst code` by
    (simp[MEM_EL] >> qexists `k - s.vs_inst_idx` >> simp[] >> decide_tac) >>
  metis_tac[]
QED

Theorem ctor_word_sequence_history:
  compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi (DecPrimWord clamp) st = ((),st') /\
  fn_has_code st st' func /\ alloca_history func s /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts /\
  t.vs_allocas = s.vs_allocas /\ t.vs_current_bb = s.vs_current_bb ==>
  alloca_history func (t with vs_inst_idx := LENGTH st'.cs_current_insts)
Proof
  strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_clamped_word_shape >> strip_tac >>
  `?bb. lookup_block st.cs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX st'.cs_current_insts bb.bb_instructions` by
    (gvs[fn_has_code_def] >> metis_tac[]) >>
  `?code. st'.cs_current_insts = st.cs_current_insts ++ code /\
          emitted_insts st st' = code` by
    (qpat_x_assum `isPREFIX st.cs_current_insts st'.cs_current_insts` mp_tac >>
     simp[IS_PREFIX_APPEND] >> strip_tac >>
     simp[emitted_insts_def, DROP_LENGTH_APPEND]) >>
  `isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `isPREFIX st'.cs_current_insts _` mp_tac >>
     simp[IS_PREFIX_APPEND] >> strip_tac >> simp[IS_PREFIX_APPEND] >>
     rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> ALLOCA) code` by
    (fs[EVERY_MEM] >> rpt strip_tac >> first_x_assum drule >>
     simp[is_alloca_op_def] >> metis_tac[]) >>
  `alloca_history func (t with vs_inst_idx := s.vs_inst_idx + LENGTH code)` by
    (irule ctor_sequence_history_advance >>
     qexistsl [`bb`, `code`, `s`] >> gvs[]) >>
  gvs[]
QED

Theorem ctor_checked_word_sequence:
  compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi (DecPrimWord clamp) st = ((),st') /\
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  abi_decoder_metadata ce env ty tv root_di av v /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  sb < dimword (:256) /\ d < dimword (:256) /\
  mem_bytes_at sb 32 initial.vs_data_section = enc (vyper_to_abi_type env ty) av /\
  sb + 32 <= LENGTH initial.vs_data_section /\ d + 32 <= initial.vs_alloca_next /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  fn_has_code st st' func /\ alloca_history func initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. run_inst_seq (emitted_insts st st') initial = OK actual /\
    val_in_memory tv v d actual.vs_memory /\ fresh_vars_wrt limit_st actual /\
    abi_decode_frame d 32 initial actual /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w) /\
    actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
    actual.vs_current_bb = initial.vs_current_bb /\
    gas_path_mem ctx func initial 0
      (OK (actual with vs_inst_idx := LENGTH st'.cs_current_insts)) /\
    actual.vs_gas_readings = initial.vs_gas_readings /\
    alloca_history func (actual with vs_inst_idx := LENGTH st'.cs_current_insts)
Proof
  strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  `mem_bytes_at sb 32 (abi_decode_source DLOAD initial) =
    enc (vyper_to_abi_type env ty) av` by simp[abi_decode_source_def] >>
  drule_all abi_decoder_primitive_clamp >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts st st') initial` by
    (irule ctor_word_reentry_mem_ok >> metis_tac[]) >>
  drule_all ctor_actual_word_ceiling_sequence >> strip_tac >>
  drule_all ctor_word_sequence_zero_path >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all abi_decoder_word_reentry_code >> strip_tac >>
  drule_all ctor_actual_sequence_world >> strip_tac >>
  drule_all abi_decoder_clamped_word_shape >> strip_tac >>
  `actual.vs_current_bb = initial.vs_current_bb` by
    (drule_at (Pos hd)
       (Q.ISPEC `\s:venom_state. s.vs_current_bb` run_inst_seq_preserves_field) >>
     simp[] >> disch_then irule >> rpt strip_tac >> fs[EVERY_MEM] >>
     metis_tac[venomInstProofsTheory.step_preserves_control_flow, step_inst_non_invoke]) >>
  `alloca_history func (actual with vs_inst_idx := LENGTH st'.cs_current_insts)` by
    (drule_all ctor_word_sequence_history >> simp[]) >>
  qexists `actual` >> simp[]
QED

Theorem ctor_word_path_sim:
  gas_path_mem ctx func s n (OK t) ==>
  ~t.vs_halted /\ abi_decode_sim ctx func s t
Proof
  strip_tac >> drule gas_path_mem_exec >>
  simp[abiDecoderLoopTheory.abi_decode_sim_def, exit_result_def] >> metis_tac[]
QED

Theorem ctor_checked_word_run:
  compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi (type_to_abi_dec_info sf ce ty) st = ((),st') /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  abi_decoder_coherent ce env sf ty tv /\ abi_decoder_metadata ce env ty tv root_di av v /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  sb + LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
  mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) av))
    initial.vs_data_section = enc (vyper_to_abi_type env ty) av /\
  sb + LENGTH (enc (vyper_to_abi_type env ty) av) <= LENGTH initial.vs_data_section /\
  (!x. src = Var x \/ dst = Var x \/ hi = Var x ==> not_fresh_at st x) /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  fn_has_code st st' func /\ fn_inst_ids_distinct func /\
  (st.cs_blocks = st'.cs_blocks \/
    !bb. lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  alloca_inv initial /\ alloca_frontier_inv ctx func site initial /\
  alloca_history func initial /\ unit_alloca_budget ctx < dimword (:256) /\
  D <= d /\ d + type_memory_bytes ce ty <= D+N /\ D+N <= initial.vs_alloca_next /\
  ctor_actual_scratch func ids D N initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. val_in_memory tv v d actual.vs_memory /\
    abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st'))
      [(d,type_memory_bytes ce ty)] initial actual /\
    alloca_inv actual /\ alloca_frontier_inv ctx func site actual /\
    ctor_actual_scratch func ids D N actual /\ D+N <= actual.vs_alloca_next /\
    actual.vs_data_section = initial.vs_data_section /\ actual.vs_call_ctx = initial.vs_call_ctx /\
    (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==> lookup_var x actual = SOME w) /\
    ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
    actual.vs_inst_idx = LENGTH st'.cs_current_insts /\ abi_decode_sim ctx func initial actual /\
    fresh_vars_wrt limit_st actual /\ actual.vs_allocas = initial.vs_allocas /\
    actual.vs_alloca_next = initial.vs_alloca_next /\ actual.vs_labels = initial.vs_labels /\
    gas_path_mem ctx func initial 0 (OK actual) /\
    actual.vs_gas_readings = initial.vs_gas_readings /\ alloca_history func actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_primitive_cases >> disch_then (qspec_then `clamp` mp_tac) >>
  asm_simp_tac bool_ss [] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `LENGTH (enc (vyper_to_abi_type env ty) av) = 32` by
    (qpat_assum `abi_decoder_metadata _ _ _ _ _ _ _`
       (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_metadata_def]) >>
     drule_all abi_decoder_descended_encoding_length >> simp[]) >>
  `sb < dimword (:256) /\ d < dimword (:256) /\ d + 32 <= initial.vs_alloca_next` by
    (drule_all alloca_frontier_inv_bound >> asm_simp_tac bool_ss [] >> decide_tac) >>
  `abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst` by
    (Cases_on `src` >> Cases_on `dst` >>
     simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
     metis_tac[not_fresh_at_def]) >>
  `compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi (DecPrimWord clamp) st = ((),st') /\
   mem_bytes_at sb 32 initial.vs_data_section = enc (vyper_to_abi_type env ty) av /\
   sb + 32 <= LENGTH initial.vs_data_section` by metis_tac[] >>
  drule_all ctor_checked_word_sequence >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all ctor_word_path_sim >> strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_word_reentry_code >> strip_tac >>
  drule_all abi_decoder_clamped_word_shape >> strip_tac >>
  drule_all ctor_actual_sequence_labels >> strip_tac >>
  drule_all ctor_actual_sequence_world >> strip_tac >>
  drule_all ctor_actual_scratch_free_effect >>
  disch_then (qspecl_then [`site`, `ctor_actual_sites func (frag_ids st st')`, `func`, `ctx`] strip_assume_tac) >>
  qexists `actual with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  simp[] >> conj_tac
  >- (qpat_x_assum `abi_encoder_registered_effect _ _ _ _` mp_tac >>
      simp[abi_encoder_registered_effect_def]) >>
  conj_tac
  >- (qpat_x_assum `ctor_actual_scratch _ _ _ _ _` mp_tac >>
      simp[ctorAbiActualFrameTheory.ctor_actual_scratch_def]) >>
  qpat_x_assum `abi_decode_frame _ _ _ _` mp_tac >>
  simp[abi_decode_frame_def] >> strip_tac >> simp[] >>
  reverse conj_tac
  >- (qpat_x_assum `fresh_vars_wrt _ actual` mp_tac >> simp[fresh_vars_wrt_def]) >>
  rpt strip_tac >>
  `abi_decoder_operand_live st.cs_next_var (Var x)` by
    (simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
     metis_tac[not_fresh_at_def]) >>
  `eval_operand (Var x) initial = SOME w` by simp[eval_operand_def] >>
  first_x_assum drule_all >> simp[eval_operand_def, lookup_var_def]
QED
