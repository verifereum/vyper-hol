(* Strong finite machine effects for primitive word decoding. *)
Theory abiDecoderWordOutcome
Ancestors
  valueEncodingDefs
  abiDecoderClampedWord abiDecoderClampOutcome abiDecoderSiteEffect
  abiDecoderRange abiDecoderClamp abiDecoderUnsignedClamp abiDecoderGuards
  abiDecoderContract abiDecoderReservation abiEncoder emitHelperProps
  exprLoweringProps compileEnv emitHelper valueEncoding valueEncodingProps
  venomExecSemantics venomState venomInst words arithmetic list rich_list pred_set

Definition abi_word_opcode_def:
  abi_word_opcode opc <=>
    opc = ADD \/ opc = MLOAD \/ opc = CALLDATALOAD \/ opc = DLOAD \/
    opc = EQ \/ opc = SIGNEXTEND \/ opc = SHL \/ opc = SHR \/
    opc = ISZERO \/ opc = ASSERT \/ opc = MSTORE
End

Theorem abi_word_step_static:
  abi_word_opcode inst.inst_opcode /\ step_inst_base inst s = OK t ==>
  t = s with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory|>
Proof
  simp_tac bool_ss [abi_word_opcode_def] >>
  disch_then (CONJUNCTS_THEN2 strip_assume_tac assume_tac) >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  PURE_ONCE_REWRITE_TAC [step_inst_base_def] >> asm_rewrite_tac [opcode_case_def] >>
  simp[exec_pure1_def, exec_pure2_def, exec_read1_def, exec_write2_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[update_var_def, mstore_def, write_memory_with_expansion_def] >>
  simp[venom_state_component_equality]
QED

Theorem abi_word_sequence_static:
  !insts s t. EVERY (\i. abi_word_opcode i.inst_opcode) insts /\
  run_inst_seq insts s = OK t ==>
  t = s with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory|>
Proof
  Induct >> simp[run_inst_seq_def] >> rpt strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  drule_all abi_word_step_static >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  fs[venom_state_component_equality]
QED

Theorem abi_decoder_word_opcodes:
  compile_abi_decode_to_buf dst src opc base_op hi (DecPrimWord clamp) st = ((),st') /\
  abi_decode_source_opcode opc ==>
  EVERY (\i. abi_word_opcode i.inst_opcode) (emitted_insts st st')
Proof
  Cases_on `base_op = Lit 0w` >> Cases_on `clamp` >>
  simp[compile_abi_decode_to_buf_def, compile_abi_dec_addr_def,
       compile_abi_decode_static_def, compile_abi_clamp_basetype_def,
       compile_abi_int_clamp_def, compile_abi_bytes_clamp_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def,
       emit_void_def, fresh_var_def, fresh_id_def, emit_def, emitted_insts_def,
       COND_RATOR, COND_RAND, AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  gvs[DROP_LENGTH_APPEND, mk_inst_def, abi_decode_source_opcode_def,
      abi_word_opcode_def] >>
  Cases_on `b` >> gvs[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >> gvs[DROP_LENGTH_APPEND]
QED

Theorem abi_word_frame_memory:
  abi_decode_frame d 32 s t /\ {a | d <= a /\ a < d+32} SUBSET writes ==>
  decode_memory_frame writes s t
Proof
  rw[decode_memory_frame_def] >> Cases_on `n = 0` >- simp[mem_bytes_at_def] >>
  `p+n <= d \/ d+32 <= p` suffices_by metis_tac[abi_decode_frame_def] >>
  fs[SUBSET_DEF] >>
  Cases_on `p+n <= d` >- simp[] >> Cases_on `d+32 <= p` >- simp[] >>
  Cases_on `p <= d`
  >- (first_x_assum (qspec_then `d` mp_tac) >>
      first_x_assum (qspec_then `d` mp_tac) >> simp[] >> decide_tac) >>
  first_x_assum (qspec_then `p` mp_tac) >>
  first_x_assum (qspec_then `p` mp_tac) >> simp[] >> decide_tac
QED

Theorem abi_decoder_word_success_effect:
  compile_abi_decode_to_buf dst src opc base_op hi (DecPrimWord clamp) st = ((),st') /\
  abi_decode_source_opcode opc /\ eval_operand src s = SOME (n2w pos) /\
  eval_operand base_op s = SOME (n2w B) /\ eval_operand dst s = SOME (n2w d) /\
  d < dimword (:256) /\
  abi_decoder_clamp_valid clamp (abi_decode_load opc (n2w (B+pos):bytes32) s) /\
  fresh_vars_wrt st s /\ decode_site_resources ctx fn s /\
  {a | d <= a /\ a < d+32} SUBSET writes /\ d+32 <= s.vs_alloca_next ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    mem_word_at d t.vs_memory = abi_decode_load opc (n2w (B+pos):bytes32) s /\
    fresh_vars_wrt st' t /\
    (!op v. eval_operand op s = SOME v ==> eval_operand op t = SOME v) /\
    decode_site_effect ctx fn next writes s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> drule_all abi_decoder_clamped_word_sequence >> strip_tac >>
  drule_all abi_decoder_word_opcodes >> strip_tac >>
  drule_all abi_word_sequence_static >> strip_tac >>
  `decode_static_frame s t` by
    fs[decode_static_frame_def, venom_state_component_equality] >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
   t.vs_fmp = s.vs_fmp` by fs[venom_state_component_equality] >>
  `decode_site_resources ctx fn t` by metis_tac[decode_site_resources_fields] >>
  `decode_memory_frame writes s t` by metis_tac[abi_word_frame_memory] >>
  `decode_upper_frame s t` by
    (match_mp_tac (Q.SPECL [`d`, `32`] decode_upper_frame_outside) >>
     reverse conj_tac >- fs[] >>
     qpat_x_assum `abi_decode_frame _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [abi_decode_frame_def]) >>
     rpt strip_tac >>
     qpat_x_assum `!p k. _ ==> mem_bytes_at p k _ = _` irule >> decide_tac) >>
  qexists `t` >> simp[decode_site_effect_def]
QED

Theorem abi_decoder_word_revert:
  compile_abi_decode_to_buf dst src opc base_op hi (DecPrimWord clamp) st = ((),st') /\
  abi_decode_source_opcode opc /\ eval_operand src s = SOME (n2w pos) /\
  eval_operand base_op s = SOME (n2w B) /\
  ~abi_decoder_clamp_valid clamp (abi_decode_load opc (n2w (B+pos):bytes32) s) /\
  abi_decoder_clamp_wf clamp /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
Proof
  simp_tac bool_ss [compile_abi_decode_to_buf_def, compile_abi_decode_static_def,
    comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rename1 `compile_abi_dec_addr base_op src st = (addr,addr_st)` >>
  rename1 `compile_abi_clamp_basetype val_op clamp c1 = ((),c2)` >>
  drule_all compile_abi_dec_addr_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st addr_st) s = OK sa` >>
  `abi_decode_load opc (n2w (B+pos):bytes32) sa =
   abi_decode_load opc (n2w (B+pos):bytes32) s` by
    gvs[abi_decode_load_def, abi_decode_source_def, mload_def] >>
  drule_all abi_decode_read >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts addr_st c1) sa = OK s1` >>
  gvs[] >> drule_all abi_decoder_clamp_revert >> strip_tac >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  `inst_extends st addr_st` by
    (Cases_on `base_op = Lit 0w` >>
     gvs[compile_abi_dec_addr_def, comp_return_def, inst_extends_refl] >>
     metis_tac[inst_extends_emit_op]) >>
  `inst_extends c1 c2` by
    (drule abi_decoder_clamp_shape >>
     simp[inst_extends_def, emitted_insts_def, IS_PREFIX_APPEND] >>
     rpt strip_tac >> gvs[DROP_LENGTH_APPEND]) >>
  `run_inst_seq (emitted_insts c1 st') s1 =
   Abort Revert_abort t` by
    (irule run_inst_seq_abort_extends >> qexists `c2` >> simp[]) >>
  `run_inst_seq (emitted_insts addr_st st') sa =
   run_inst_seq (emitted_insts c1 st') s1` by
    (irule run_inst_seq_emit_extend >> simp[] >> metis_tac[inst_extends_trans]) >>
  `run_inst_seq (emitted_insts st st') s =
   run_inst_seq (emitted_insts addr_st st') sa` by
    (irule run_inst_seq_emit_extend >> simp[] >> metis_tac[inst_extends_trans]) >>
  metis_tac[]
QED

Theorem abi_decoder_word_finite_outcome:
  compile_abi_decode_to_buf dst src opc base_op hi (DecPrimWord clamp) st = ((),st') /\
  abi_decode_source_opcode opc /\ eval_operand src s = SOME (n2w pos) /\
  eval_operand base_op s = SOME (n2w B) /\ eval_operand dst s = SOME (n2w d) /\
  eval_operand hi s = SOME (n2w H) /\ pos+32 <= H /\
  B+H < dimword (:256) /\ d+32 < dimword (:256) /\
  fresh_vars_wrt st s /\ abi_decoder_clamp_wf clamp /\
  decode_site_resources ctx fn s /\ {a | d <= a /\ a < d+32} SUBSET writes /\
  d+32 <= s.vs_alloca_next ==>
  ((?t. run_inst_seq (emitted_insts st st') s = OK t /\
    abi_decoder_clamp_valid clamp (abi_decode_load opc (n2w (B+pos):bytes32) s) /\
    mem_word_at d t.vs_memory = abi_decode_load opc (n2w (B+pos):bytes32) s /\
    fresh_vars_wrt st' t /\
    (!op v. eval_operand op s = SOME v ==> eval_operand op t = SOME v) /\
    decode_site_effect ctx fn next writes s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next) \/
   (?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t /\
    ~abi_decoder_clamp_valid clamp (abi_decode_load opc (n2w (B+pos):bytes32) s)))
Proof
  strip_tac >>
  Cases_on `abi_decoder_clamp_valid clamp (abi_decode_load opc (n2w (B+pos):bytes32) s)`
  >- (disj1_tac >> `d < dimword (:256)` by decide_tac >>
      drule_all abi_decoder_word_success_effect >> metis_tac[]) >>
  disj2_tac >> drule_all abi_decoder_word_revert >> metis_tac[]
QED

Theorem abi_decoder_word_inst_extends:
  compile_abi_decode_to_buf dst src opc base_op hi (DecPrimWord clamp) st = ((),st') /\
  abi_decode_source_opcode opc ==> inst_extends st st'
Proof
  strip_tac >> drule_all abi_decoder_clamped_word_shape >>
  simp[inst_extends_def, emitted_insts_def, IS_PREFIX_APPEND] >>
  rpt strip_tac >> gvs[DROP_LENGTH_APPEND]
QED
