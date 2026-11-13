(* Counted memory-safe run of abi_encode over a staged source buffer:
   the three counted phases, with S1's staged observation of the result.
   Shared by the word and tuple cases. *)
Theory bodyMemTbAbiEncodeStaged
Ancestors
  bodyMemTbAbiEncodePhases exprSimAbiEncodeStagedObserver
  loweringStateRelDefs exprSimAbiEncodeStateTransport exprSimAbiEncodeExecFrame
  abiBuiltinEncodeSetup abiEncoderWindowContract abiBuiltinAllocation
  abiBuiltinEncodeCode abiDecoderReentry compileEnv exprLoweringProps
  fragGasPathMem venomState venomMemDefs loweringPosts finite_map words list

Theorem abi_encode_staged_mem:
  abi_builtin_encode_setup method_id maxlen st = (ops,ready) /\
  compile_abi_encode_to_buf (SND ops) src ei ready = (len,body_end) /\
  abi_builtin_encode_finish (FST ops) len m body_end = ((),final) /\
  m = (case method_id of NONE => 0 | SOME mid => 4) /\
  w = (case method_id of NONE => 0 | SOME mid => 32) /\
  d = p+32+m /\ outsz = 32+32*word_size (maxlen+m) /\
  fn_has_code st final func /\
  fn_has_code st ready func /\ fn_has_code ready body_end func /\
  fn_has_code body_end final func /\ fn_inst_ids_distinct func /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,outsz)) /\
  outsz < dimword (:256) /\ p < dimword (:256) /\
  (method_id <> NONE ==> p+32 < dimword (:256)) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  abi_encoder_admissible ei /\ abi_encoder_window_input ei at av sb cap initial.vs_memory /\
  0 < cap /\
  eval_operand src initial = SOME (n2w sb) /\ abi_decoder_operand_live st.cs_next_var src /\
  (!x. src = Var x \/ SND ops = Var x ==> not_fresh_at ready x) /\
  (!x. FST ops = Var x ==> not_fresh_at ready x) /\
  abi_decoder_operand_live body_end.cs_next_var (FST ops) /\
  alloca_inv (abi_builtin_allocate_state st.cs_next_id outsz initial) /\
  alloca_room ctx func (abi_builtin_allocate_state st.cs_next_id outsz initial) /\
  sb+cap <= (abi_builtin_allocate_state st.cs_next_id outsz initial).vs_alloca_next /\
  d+LENGTH (enc at av) <= (abi_builtin_allocate_state st.cs_next_id outsz initial).vs_alloca_next /\
  venomMemDefs$regions_disjoint (sb,cap) (d,LENGTH (enc at av)) /\
  (sb+cap <= p+32 \/ p+32+w <= sb) /\
  venomMemDefs$regions_disjoint (p+32,m) (d,LENGTH (enc at av)) /\
  (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids ready body_end /\
    FLOOKUP (abi_builtin_allocate_state st.cs_next_id outsz initial).vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\ venomMemDefs$regions_disjoint (sb,cap) (b,sz) /\
    venomMemDefs$regions_disjoint (d,LENGTH (enc at av)) (b,sz) /\
    venomMemDefs$regions_disjoint (p+32,m) (b,sz)) /\
  stmt_state_rel ctx func ce cx vs initial /\ local_ptrs_reserved ce st /\
  st.cs_next_var <= ready.cs_next_var /\ st.cs_next_var <= body_end.cs_next_var /\
  32+w <= outsz /\ p <= d /\ d+LENGTH (enc at av) <= p+outsz ==>
  ?n actual.
    gas_path_mem ctx func initial n (OK actual) /\
    ~actual.vs_halted /\ actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    abi_encode_exec_frame func initial actual /\
    initial.vs_alloca_next <= actual.vs_alloca_next /\
    abi_encode_staged_observation ctx func ce cx vs st (FST ops) method_id
      outsz p at av initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `cap = 0 ==> (ei = AbiCopy 0 \/ ei = AbiComplex []) /\ enc at av = []` by
    (strip_tac >> qpat_x_assum `0 < cap` mp_tac >>
     qpat_x_assum `cap = 0` SUBST1_TAC >> simp_tac arith_ss []) >>
  `0 < cap ==>
    sb+cap <= (abi_builtin_allocate_state st.cs_next_id outsz initial).vs_alloca_next /\
    venomMemDefs$regions_disjoint (sb,cap) (d,LENGTH (enc at av)) /\
    (sb+cap <= p+32 \/ p+32+w <= sb)` by
    (strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  drule_all abi_encode_phases_mem >>
  disch_then (qx_choosel_then [`n`, `actual`] strip_assume_tac) >>
  `!j. MEM j (fn_insts func) /\ j.inst_opcode <> STOP /\
    j.inst_opcode <> NOP ==> MEM j (fn_insts func)` by simp[] >>
  drule_all abi_encode_caller_phase_allocations >> strip_tac >>
  `outsz = 32+32*word_size (maxlen+(case method_id of NONE => 0 | SOME x => 4))` by
    (qpat_assum `outsz = _` (fn th => rewrite_tac [th]) >>
     qpat_assum `m = _` (fn th => rewrite_tac [th])) >>
  drule_all abi_encode_phases_caller_state >> strip_tac >>
  drule_all abi_encode_phases_caller_pure_frame >> strip_tac >>
  `alloca_inv actual` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ actual` mp_tac >>
     simp_tac bool_ss [stmt_state_rel_def] >> strip_tac >> first_assum ACCEPT_TAC) >>
  `st.cs_next_id <= ready.cs_next_id` by
    (drule abi_builtin_encode_setup_shape >> strip_tac >>
     qpat_assum `ready.cs_next_id = _` (fn th => rewrite_tac [th]) >>
     simp_tac arith_ss []) >>
  suspend "frame"
QED

Resume abi_encode_staged_mem[frame]:
  `!aid off sz. FLOOKUP initial.vs_allocas aid = SOME(off,sz) /\ aid < st.cs_next_id ==>
    mem_bytes_at off sz actual.vs_memory = mem_bytes_at off sz initial.vs_memory` by
    (rpt gen_tac >> strip_tac >>
     irule abi_encode_caller_phase_old_rows >>
     qpat_assum `abi_builtin_encode_setup_frame _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `window_strong_result _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     qexists_tac `aid` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!x v. not_fresh_at st x /\ lookup_var x initial = SOME v ==>
    lookup_var x actual = SOME v` by
    (rpt gen_tac >> strip_tac >>
     `abi_decoder_operand_live st.cs_next_var (Var x)` by
       (qpat_assum `not_fresh_at st x` mp_tac >>
        simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def,
          not_fresh_at_def, IN_DEF]) >>
     irule abi_encode_caller_phase_registers >>
     qpat_assum `abi_builtin_encode_setup_frame _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `window_strong_result _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `initial.vs_alloca_next <= actual.vs_alloca_next` by
    (qpat_assum `window_alloca_growth initial actual` mp_tac >>
     simp_tac bool_ss [window_alloca_growth_def] >> disch_then (ACCEPT_TAC o CONJUNCT1)) >>
  qpat_assum `abi_encode_exec_frame func initial actual` mp_tac >>
  simp_tac bool_ss [abi_encode_exec_frame_def] >> strip_tac >>
  qexistsl_tac [`n`, `actual`] >>
  rewrite_tac [abi_encode_staged_observation_def] >>
  qpat_assum `m = _` (fn th => rewrite_tac [GSYM th]) >>
  qpat_assum `d = _` (fn th => rewrite_tac [GSYM th]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
Finalise abi_encode_staged_mem
