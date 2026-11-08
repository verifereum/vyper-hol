Theory exprSimAbiEncodeStagedRawObserver
Ancestors
  exprSimAbiEncodeStagedObserver exprSimAbiEncodeTranslatedPhases
  exprSimAbiEncodeStateTransport exprSimAbiEncodeCallerSuffix
  exprSimAbiEncodeExecFrame abiBuiltinEncodeSetup abiEncoderWindowContract
  exprLoweringProps compileEnv venomState words list loweringPosts abiBuiltinEncodeCode abiDecoderReentry

Theorem abi_encode_staged_raw_observer:
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
    venomMemDefs$regions_disjoint (p+32,m) (b,sz)) /\
  stmt_state_rel ctx func ce cx vs initial /\ local_ptrs_reserved ce st /\
  st.cs_next_var <= ready.cs_next_var /\ st.cs_next_var <= body_end.cs_next_var /\
  32+w <= outsz /\ p <= d /\ d+LENGTH(enc at av) <= p+outsz ==>
  ?raw. run_inst_seq (emitted_insts st final) initial = OK raw /\
    let actual = raw with vs_inst_idx := LENGTH final.cs_current_insts in
    ~actual.vs_halted /\ actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    abi_encode_exec_frame func initial actual /\
    abi_encode_staged_observation ctx func ce cx vs st (FST ops) method_id outsz p at av initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_translated_concrete_phases >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `abi_encode_exec_frame func initial actual` >>
  drule_all abi_encode_caller_phase_allocations >> strip_tac >>
  `outsz = 32+32*word_size (maxlen+(case method_id of NONE => 0 | SOME x => 4))` by
    (qpat_assum `outsz = _` (fn th => rewrite_tac [th]) >>
     qpat_assum `m = _` (fn th => rewrite_tac [th])) >>
  `!j. MEM j (fn_insts func) /\ j.inst_opcode <> STOP /\ j.inst_opcode <> NOP ==>
    MEM j (fn_insts func)` by simp[] >>
  drule_all abi_encode_phases_caller_state >> strip_tac >>
  `alloca_inv actual` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ actual` mp_tac >>
     simp_tac bool_ss [stmt_state_rel_def] >> strip_tac >> first_assum ACCEPT_TAC) >>
  `st.cs_next_id <= ready.cs_next_id` by
    (drule abi_builtin_encode_setup_shape >> strip_tac >>
     qpat_assum `ready.cs_next_id = _` (fn th => rewrite_tac [th]) >> simp_tac arith_ss []) >>
  `!aid off sz. FLOOKUP initial.vs_allocas aid = SOME(off,sz) /\ aid < st.cs_next_id ==>
    mem_bytes_at off sz actual.vs_memory = mem_bytes_at off sz initial.vs_memory` by
    (rpt gen_tac >> strip_tac >> irule abi_encode_caller_phase_old_rows >>
     qpat_assum `abi_builtin_encode_setup_frame _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `window_strong_result _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     qexists_tac `aid` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!x v. not_fresh_at st x /\ lookup_var x initial = SOME v ==> lookup_var x actual = SOME v` by
    (rpt gen_tac >> strip_tac >>
     `abi_decoder_operand_live st.cs_next_var (Var x)` by
       (qpat_assum `not_fresh_at st x` mp_tac >>
        simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def, IN_DEF]) >>
     irule abi_encode_caller_phase_registers >>
     qpat_assum `abi_builtin_encode_setup_frame _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `window_strong_result _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `abi_encode_exec_frame func initial actual` mp_tac >>
  simp_tac bool_ss [abi_encode_exec_frame_def] >> strip_tac >>
  qexists_tac `raw` >> simp_tac bool_ss [LET_THM] >>
  qpat_x_assum `Abbrev (actual = _)`
    (fn th => rewrite_tac[GSYM (PURE_REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  asm_rewrite_tac[abi_encode_staged_observation_def] >>
  qpat_assum `m = _` (fn th => rewrite_tac [GSYM th]) >>
  qpat_assum `d = _` (fn th => rewrite_tac [GSYM th]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
