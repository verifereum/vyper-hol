Theory exprSimAbiEncodeTranslatedPhases
Ancestors
  valueEncodingDefs
  exprSimAbiEncodeNonwordNoBlock exprSimAbiEncodeEmptyComplex
  exprSimAbiEncodeConcreteBuiltinWrappers exprSimAbiEncodeConcreteCompose
  exprSimAbiEncodeConcreteWrappers exprSimAbiEncodeNoBlockFrame
  exprSimAbiEncodeFramedBuiltin exprSimAbiEncodeExecFrame
  abiEncodeWindowBuiltin abiEncoderWindowContract abiDecoderContract
  abiEncoderRegisteredEffect abiEncoderExtendSim abiEncoderWindowLeaves
  abiBuiltinEncodeCode abiBuiltinEncodeSetup abiBuiltinEncodeContext
  exprSimAbiEncodeTranslatedZero exprLoweringProps emitHelperProps
  compileEnv venomState list words emitHelper venomInst rich_list exprLowering context abiEncoderWindow exprSimAbiEncodeEmptySource

Theorem abi_encode_translated_setup_opcodes[local]:
  abi_builtin_encode_setup mid maxlen st = (ops,ready) ==>
  EVERY (\i. MEM i.inst_opcode [ALLOCA;ADD;MSTORE]) (emitted_insts st ready)
Proof
  Cases_on `mid` >>
  simp[abi_builtin_encode_setup_def, abi_builtin_encode_method_id_def,
    compile_alloc_buffer_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def]
QED

Theorem abi_encode_translated_concrete_phases:
  abi_builtin_encode_setup method_id maxlen st = (ops,ready) /\
  compile_abi_encode_to_buf (SND ops) src ei ready = (len,body_end) /\
  abi_builtin_encode_finish (FST ops) len m body_end = ((),final) /\
  m = (case method_id of NONE => 0 | SOME mid => 4) /\
  w = (case method_id of NONE => 0 | SOME mid => 32) /\
  d = p+32+m /\ outsz = 32+32*word_size (maxlen+m) /\
  fn_has_code st ready func /\ fn_has_code ready body_end func /\
  fn_has_code body_end final func /\ fn_inst_ids_distinct func /\
  st.cs_blocks = final.cs_blocks /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,outsz)) /\
  outsz < dimword (:256) /\ p < dimword (:256) /\
  (method_id <> NONE ==> p+32 < dimword (:256)) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  abi_encoder_admissible ei /\ abi_encoder_window_input ei at av sb cap initial.vs_memory /\
  eval_operand src initial = SOME (n2w sb) /\ abi_decoder_operand_live st.cs_next_var src /\
  (!x. src = Var x \/ SND ops = Var x ==> not_fresh_at ready x) /\
  (!x. FST ops = Var x ==> not_fresh_at ready x) /\
  abi_decoder_operand_live body_end.cs_next_var (FST ops) /\
  alloca_inv (abi_builtin_allocate_state st.cs_next_id outsz initial) /\
  alloca_room ctx func (abi_builtin_allocate_state st.cs_next_id outsz initial) /\
  (cap = 0 ==> (ei = AbiCopy 0 \/ ei = AbiComplex []) /\ enc at av = []) /\
  (0 < cap ==>
    sb+cap <= (abi_builtin_allocate_state st.cs_next_id outsz initial).vs_alloca_next /\
    venomMemDefs$regions_disjoint (sb,cap) (d,LENGTH (enc at av)) /\
    (sb+cap <= p+32 \/ p+32+w <= sb)) /\
  d+LENGTH (enc at av) <= (abi_builtin_allocate_state st.cs_next_id outsz initial).vs_alloca_next /\
  venomMemDefs$regions_disjoint (p+32,m) (d,LENGTH (enc at av)) /\
  (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids ready body_end /\
    FLOOKUP (abi_builtin_allocate_state st.cs_next_id outsz initial).vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\ venomMemDefs$regions_disjoint (sb,cap) (b,sz) /\
    venomMemDefs$regions_disjoint (d,LENGTH (enc at av)) (b,sz) /\
    venomMemDefs$regions_disjoint (p+32,m) (b,sz)) ==>
  ?raw. run_inst_seq (emitted_insts st final) initial = OK raw /\
    let actual = raw with vs_inst_idx := LENGTH final.cs_current_insts in
    eval_operand (FST ops) actual = SOME (n2w p) /\
    mload p actual = n2w (LENGTH (enc at av)+m) /\
    mem_bytes_at d (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    (case method_id of NONE => T | SOME mid =>
      mem_bytes_at (p+32) 4 actual.vs_memory = abi_builtin_encode_method_bytes mid) /\
    ~actual.vs_halted /\ actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    abi_encode_exec_frame func initial actual /\
    ?prepared body_state.
      abi_builtin_encode_setup_frame st.cs_next_var st.cs_next_id outsz p w initial prepared /\
      window_strong_result ctx func ready body_end len at av d prepared body_state /\
      abi_encoder_registered_effect {} [(p,32)] body_state actual /\
      actual.vs_allocas = body_state.vs_allocas /\
      actual.vs_alloca_next = body_state.vs_alloca_next /\
      (!op v. abi_decoder_operand_live body_end.cs_next_var op /\
        eval_operand op body_state = SOME v ==> eval_operand op actual = SOME v) /\
      prepared.vs_accounts = initial.vs_accounts /\
      prepared.vs_transient = initial.vs_transient /\
      prepared.vs_logs = initial.vs_logs /\
      prepared.vs_requests = initial.vs_requests /\
      prepared.vs_pending_deletions = initial.vs_pending_deletions /\
      actual.vs_labels = initial.vs_labels
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  Cases_on `cap = 0 /\ ei = AbiComplex []`
  >- suspend "complex"
  >> irule abi_encode_window_concrete_phases >>
  asm_rewrite_tac[] >>
  conj_tac >- metis_tac[] >>
  qexistsl [`cap`, `ei`, `sb`, `src`] >> asm_rewrite_tac[] >> metis_tac[]
QED

Resume abi_encode_translated_concrete_phases[complex]:
  `ei = AbiComplex [] /\ enc at av = [] /\ cap = 0` by metis_tac[] >>
  `abi_encoder_window_input ei at av 0 0 initial.vs_memory` by
    (qpat_assum `abi_encoder_window_input _ _ _ _ _ _` mp_tac >>
     qpat_assum `ei = AbiComplex []` SUBST1_TAC >>
     qpat_assum `cap = 0` SUBST1_TAC >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[Once abi_encoder_window_input_cases] >> strip_tac >>
     simp[Once abi_encoder_window_input_cases] >> metis_tac[]) >>
  qpat_assum `abi_encoder_window_input _ _ _ 0 0 _`
    (mp_then (Pat `abi_encoder_window_input _ _ _ _ _ _`) mp_tac abi_encode_window_setup_concrete) >>
  disch_then (drule_at (Pat `abi_builtin_encode_setup _ _ _ = _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (qspecl_then [`w`, `p`, `outsz`, `m`, `ctx`] mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[] >> simp_tac arith_ss [])) >>
  simp_tac bool_ss [LET_THM] >>
  disch_then (qx_choose_then `setup_raw` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  qmatch_asmsub_abbrev_tac `abi_builtin_encode_setup_frame _ _ _ _ _ initial prepared` >>
  `abi_encode_exec_frame func initial prepared` by
    (drule abi_encode_translated_setup_opcodes >> strip_tac >>
     drule_all abi_encode_setup_sequence_frame >>
     simp_tac bool_ss [Abbr `prepared`, abi_encode_exec_frame_inst_idx]) >>
  `len = Lit 0w /\ body_end = ready` by
    (qpat_assum `compile_abi_encode_to_buf _ _ _ _ = _` mp_tac >>
     qpat_assum `ei = AbiComplex []` SUBST1_TAC >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[abi_encode_empty_complex_body_probe]) >>
  `alloca_inv prepared /\ alloca_room ctx func prepared` by
    metis_tac[abi_window_setup_alloca_inv, abi_window_setup_room] >>
  `window_strong_result ctx func ready body_end len at av d prepared prepared` by
    (irule (cj 1 abi_encode_empty_complex_framed) >>
     goal_assum (drule_at (Pat `alloca_room _ _ _`)) >>
     asm_rewrite_tac[] >> qexistsl [`SND ops`, `src`] >>
     asm_rewrite_tac[] >> simp_tac bool_ss [abi_encode_empty_complex_body_probe]) >>
  suspend "finish"
QED

Resume abi_encode_translated_concrete_phases[finish]:
  drule abi_encode_window_finish_concrete >>
  disch_then (drule_at (Pat `window_strong_result _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`p`, `LENGTH (enc at av)`,
    `mem_bytes_at (p+32) (m+LENGTH (enc at av)) prepared.vs_memory`] mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[] >> simp_tac (srw_ss()) [eval_operand_def])) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts body_end final) prepared = OK finish_raw` >>
  qmatch_asmsub_abbrev_tac `abi_decode_frame p 32 prepared actual` >>
  `abi_encode_exec_frame func prepared actual` by
    (`finish_raw.vs_allocas = prepared.vs_allocas /\
      finish_raw.vs_alloca_next = prepared.vs_alloca_next` by
       (qpat_x_assum `actual.vs_allocas = _` mp_tac >>
        qpat_x_assum `actual.vs_alloca_next = _` mp_tac >>
        simp_tac (srw_ss()) [Abbr `actual`]) >>
     drule_all abi_encode_framed_finish_sequence >>
     simp_tac bool_ss [Abbr `actual`, abi_encode_exec_frame_inst_idx]) >>
  `abi_encode_exec_frame func initial actual` by metis_tac[abi_encode_exec_frame_trans] >>
  suspend "result"
QED

Resume abi_encode_translated_concrete_phases[result]:
  `mem_bytes_at d (LENGTH (enc at av)) actual.vs_memory = enc at av` by
    (qpat_assum `enc at av = []` (fn th => rewrite_tac[th]) >>
     simp_tac (srw_ss()) [valueEncodingDefsTheory.mem_bytes_at_def]) >>
  `(case method_id of NONE => T | SOME mid =>
      mem_bytes_at (p+32) 4 actual.vs_memory = abi_builtin_encode_method_bytes mid)` by
    (qpat_assum `abi_decode_frame p 32 prepared actual`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_decode_frame_def]) >>
     `mem_bytes_at (p+32) m actual.vs_memory = mem_bytes_at (p+32) m prepared.vs_memory` by
       (qpat_x_assum `!p' k. _` (qspecl_then [`p+32`, `m`] mp_tac) >>
        simp_tac bool_ss [arithmeticTheory.LE_REFL]) >>
     qpat_x_assum `mem_bytes_at (p+32) m actual.vs_memory = _` mp_tac >>
     qpat_x_assum `case method_id of NONE => T | SOME mid => _` mp_tac >>
     qpat_x_assum `m = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     Cases_on `method_id` >> simp_tac (srw_ss()) [] >> metis_tac[]) >>
  suspend "compose"
QED

Resume abi_encode_translated_concrete_phases[compose]:
  `?raw. run_inst_seq (emitted_insts st final) initial = OK raw /\
    (raw with vs_inst_idx := LENGTH final.cs_current_insts) = actual` by
    (qpat_x_assum `Abbrev (actual = _)`
       (SUBST_ALL_TAC o PURE_REWRITE_RULE [markerTheory.Abbrev_def]) >>
     `emitted_insts st final = emitted_insts st ready ++ emitted_insts ready final` by
       (irule emitted_insts_append >>
        qpat_assum `inst_extends st ready` mp_tac >>
        qpat_assum `inst_extends body_end final` mp_tac >>
        qpat_assum `body_end = ready` SUBST1_TAC >>
        POP_ASSUM_LIST (K all_tac) >> simp[inst_extends_def]) >>
     qpat_assum `emitted_insts st final = _` (fn th => pure_rewrite_tac[th]) >>
     irule abi_encode_run_append_normalized >>
     reverse conj_tac >- metis_tac[] >>
     qexistsl [`LENGTH ready.cs_current_insts`, `setup_raw`] >>
     asm_rewrite_tac[] >>
     simp_tac (srw_ss()) [Abbr `prepared`] >> metis_tac[]) >>
  qexists `raw` >> simp_tac bool_ss [LET_THM] >> asm_rewrite_tac[] >>
  conj_tac >- metis_tac[] >>
  qexistsl [`prepared`, `prepared`] >> asm_rewrite_tac[] >> metis_tac[]
QED
Finalise abi_encode_translated_concrete_phases
