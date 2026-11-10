Theory exprSimAbiEncodeExecution
Ancestors
  loweringStateRelDefs
  exprSimAbiEncodeConcreteResources exprSimAbiEncodeOpenSetup
  exprSimAbiEncodeFinish abiDecoderGuards abiDecoderReentry venomState
  exprSimAbiEncodeProducerAssembly exprSimAbiEncodeSourceRoom exprSimAbiEncodeWindowRoom
  abiEncoderWindowRun abiEncodeWindowBuiltin abiEncoderWindowContract
  abiEncoderWindow abiEncoderRegisteredEffect abiDecoderContract abiBuiltinEncodeCode
  abiBuiltinEncodeSetup abiBuiltinAllocation abiDecoderLoop compileEnv
  exprLoweringProps words list finite_map abiBuiltinEncodeAllocate emitHelper emitHelperProps

Theorem abi_encode_none_setup_allocate[local]:
  abi_builtin_encode_setup NONE maxlen st =
    abi_builtin_encode_allocate (32+32*word_size maxlen) 32 st
Proof
  simp[abi_builtin_encode_setup_allocate, abi_builtin_encode_method_id_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[]
QED

Theorem abi_encode_none_setup_buffer_old:
  abi_builtin_encode_setup NONE maxlen st = (ops,ready) ==>
  (!x. FST ops = Var x ==> not_fresh_at ready x)
Proof
  pure_rewrite_tac[abi_encode_none_setup_allocate] >> strip_tac >>
  drule (cj 1 abi_builtin_encode_allocate_live) >>
  Cases_on `FST ops` >>
  simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def,
    not_fresh_at_def]
QED

Theorem abi_encode_none_setup_buffer_eval:
  abi_builtin_encode_setup NONE maxlen st = (ops,ready) /\
  abi_encoder_window_result ctx func ready body_end out at av d s t /\
  eval_operand (FST ops) s = SOME w ==>
  eval_operand (FST ops) t = SOME w
Proof
  strip_tac >>
  `FST ops = Var ("%" ++ toString st.cs_next_var)` by
    (qpat_x_assum `abi_builtin_encode_setup NONE _ _ = _` mp_tac >>
     pure_rewrite_tac[abi_encode_none_setup_allocate] >> strip_tac >>
     drule abi_builtin_encode_allocate_trace >> strip_tac >>
     drule abi_builtin_alloc_buffer_shape >> strip_tac >>
     drule emitted_insts_emit_op >> strip_tac >> simp[]) >>
  drule abi_encode_none_setup_buffer_old >>
  disch_then (qspec_then `"%" ++ toString st.cs_next_var` mp_tac) >>
  pure_asm_rewrite_tac[] >> simp_tac bool_ss [] >> strip_tac >>
  qpat_x_assum `eval_operand (FST ops) s = _` mp_tac >>
  pure_asm_rewrite_tac[eval_operand_def] >> strip_tac >>
  pure_asm_rewrite_tac[eval_operand_def] >>
  drule_all abi_encoder_window_result_vars >> simp[]
QED

Theorem abi_encode_window_none_phases:
  abi_builtin_encode_setup NONE maxlen st = (ops,ready) /\
  compile_abi_encode_to_buf (SND ops) src ei ready = (len,body_end) /\
  abi_builtin_encode_finish (FST ops) len 0 body_end = ((),final) /\
  fn_has_code st ready func /\ fn_has_code ready body_end func /\
  fn_has_code body_end final func /\ fn_inst_ids_distinct func /\
  outsz = 32+32*word_size maxlen /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,outsz)) /\
  outsz < dimword (:256) /\ p < dimword (:256) /\
  ready.cs_next_var <= limit_st.cs_next_var /\ body_end.cs_next_var <= limit_st.cs_next_var /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  abi_encoder_admissible ei /\ abi_encoder_window_input ei at av sb cap initial.vs_memory /\
  eval_operand src initial = SOME (n2w sb) /\ abi_decoder_operand_live st.cs_next_var src /\
  (!x. src = Var x \/ SND ops = Var x ==> not_fresh_at ready x) /\
  abi_decoder_operand_live body_end.cs_next_var (FST ops) /\
  alloca_inv (abi_builtin_allocate_state st.cs_next_id outsz initial) /\
  alloca_room ctx func (abi_builtin_allocate_state st.cs_next_id outsz initial) /\
  sb+cap <= (abi_builtin_allocate_state st.cs_next_id outsz initial).vs_alloca_next /\
  p+32+LENGTH (enc at av) <= (abi_builtin_allocate_state st.cs_next_id outsz initial).vs_alloca_next /\
  venomMemDefs$regions_disjoint (sb,cap) (p+32,LENGTH (enc at av)) /\
  (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids ready body_end /\
    FLOOKUP (abi_builtin_allocate_state st.cs_next_id outsz initial).vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\ venomMemDefs$regions_disjoint (sb,cap) (b,sz) /\
    venomMemDefs$regions_disjoint (p+32,LENGTH (enc at av)) (b,sz)) ==>
  ?actual. eval_operand (FST ops) actual = SOME (n2w p) /\
    mload p actual = n2w (LENGTH (enc at av)) /\
    mem_bytes_at (p+32) (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    ~actual.vs_halted /\
    actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `?prepared. eval_operand (FST ops) prepared = SOME (n2w p) /\
    eval_operand (SND ops) prepared = SOME (n2w (p+32)) /\
    fresh_vars_wrt limit_st prepared /\
    abi_builtin_encode_setup_frame st.cs_next_var st.cs_next_id outsz p 0 initial prepared /\
    abi_encoder_window_input ei at av sb cap prepared.vs_memory /\
    prepared.vs_current_bb = ready.cs_current_bb /\
    prepared.vs_inst_idx = LENGTH ready.cs_current_insts /\
    ~prepared.vs_halted /\ abi_decode_sim ctx func initial prepared` by
    (`abi_builtin_encode_allocate outsz 32 st = (ops,ready)` by
       metis_tac[abi_encode_none_setup_allocate] >>
     drule abi_window_allocate_observed_reach >> disch_then drule >>
     disch_then (qspecl_then [`p`, `limit_st`, `initial`, `ctx`] mp_tac) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
     qpat_assum `abi_builtin_allocation_frame _ _ _ _ _`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_builtin_allocation_frame_def]) >>
     qexists `actual` >>
     pure_asm_rewrite_tac[abi_builtin_encode_setup_frame_def, abi_decode_frame_def] >>
     simp_tac bool_ss []) >>
  `abi_encoder_window_pre ctx func ready body_end (SND ops) src ei at av sb cap (p+32) prepared` by
    (irule (SIMP_RULE bool_ss [LET_THM] abi_encode_setup_window_pre) >>
     pure_asm_rewrite_tac[] >> simp_tac bool_ss [] >>
     qexistsl [`initial`, `st.cs_next_var`, `outsz`, `p`, `st.cs_next_id`, `0`] >>
     pure_asm_rewrite_tac[] >> simp_tac bool_ss []) >>
  drule_all compile_abi_encode_to_buf_window_strong_run >> strip_tac >>
  qpat_assum `window_strong_result _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE
      [window_strong_result_def, abi_encoder_window_result_def]) >>
  `eval_operand (FST ops) actual = SOME (n2w p)` by
    (irule abi_encode_none_setup_buffer_eval >>
     goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >>
     drule window_strong_result_public >> strip_tac >>
     goal_assum (drule_at Any)) >>
  drule_all abi_encode_finish_reach_open >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `mem_bytes_at (p+32) (LENGTH (enc at av)) actual'.vs_memory = enc at av` by
    (qpat_x_assum `abi_decode_frame p 32 actual actual'` mp_tac >>
     pure_rewrite_tac[abi_decode_frame_def] >> strip_tac >>
     qpat_x_assum `!p' k. _` (qspecl_then [`p+32`, `LENGTH (enc at av)`] mp_tac) >>
     (impl_tac >- decide_tac) >>
     disch_then SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `mload p actual' = _` (assume_tac o SIMP_RULE bool_ss [arithmeticTheory.ADD_0]) >>
  qexists `actual'` >>
  simp_tac bool_ss [arithmeticTheory.ADD_0] >>
  rpt conj_tac >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC >>
  irule abi_decode_sim_trans >> qexists `prepared` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule abi_decode_sim_trans >> qexists `actual` >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Theorem abi_encode_setup_buffer_eval:
  window_strong_result ctx func ready body_end out at av d s t /\
  (!x. buf = Var x ==> not_fresh_at ready x) /\
  eval_operand buf s = SOME w ==>
  eval_operand buf t = SOME w
Proof
  strip_tac >>
  qpat_assum `window_strong_result _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [window_strong_result_def]) >>
  Cases_on `buf` >>
  gvs[eval_operand_def] >>
  drule_all abi_encoder_window_result_vars >> simp[]
QED

Theorem abi_encode_window_phases_open:
  abi_builtin_encode_setup method_id maxlen st = (ops,ready) /\
  compile_abi_encode_to_buf (SND ops) src ei ready = (len,body_end) /\
  abi_builtin_encode_finish (FST ops) len m body_end = ((),final) /\
  m = (case method_id of NONE => 0 | SOME mid => 4) /\
  w = (case method_id of NONE => 0 | SOME mid => 32) /\
  d = p+32+m /\ outsz = 32+32*word_size (maxlen+m) /\
  fn_has_code st ready func /\ fn_has_code ready body_end func /\
  fn_has_code body_end final func /\ fn_inst_ids_distinct func /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,outsz)) /\
  outsz < dimword (:256) /\ p < dimword (:256) /\
  (method_id <> NONE ==> p+32 < dimword (:256)) /\
  ready.cs_next_var <= limit_st.cs_next_var /\ body_end.cs_next_var <= limit_st.cs_next_var /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  abi_encoder_admissible ei /\ abi_encoder_window_input ei at av sb cap initial.vs_memory /\
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
    venomMemDefs$regions_disjoint (p+32,m) (b,sz)) ==>
  ?prepared body actual.
    eval_operand (FST ops) actual = SOME (n2w p) /\
    mload p actual = n2w (LENGTH (enc at av)+m) /\
    mem_bytes_at d (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    (case method_id of NONE => T | SOME mid =>
      mem_bytes_at (p+32) 4 actual.vs_memory = abi_builtin_encode_method_bytes mid) /\
    ~actual.vs_halted /\ actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    abi_decode_sim ctx func initial actual /\
    abi_builtin_encode_setup_frame st.cs_next_var st.cs_next_id outsz p w initial prepared /\
    window_strong_result ctx func ready body_end len at av d prepared body /\
    abi_decode_frame p 32 body actual /\
    actual.vs_allocas = body.vs_allocas /\ actual.vs_alloca_next = body.vs_alloca_next /\
    abi_encoder_registered_effect {} [(p,32)] body actual /\
    (!op v. abi_decoder_operand_live body_end.cs_next_var op /\ eval_operand op body = SOME v ==>
      eval_operand op actual = SOME v)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_window_setup_observed >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_builtin_encode_setup_frame _ _ _ _ _ initial prepared` >>
  `abi_encoder_window_pre ctx func ready body_end (SND ops) src ei at av sb cap d prepared` by
    (qpat_x_assum `d = _` SUBST_ALL_TAC >>
     qpat_x_assum `outsz = _` SUBST_ALL_TAC >>
     qpat_x_assum `m = _` SUBST_ALL_TAC >>
     irule (SIMP_RULE bool_ss [LET_THM] abi_encode_setup_window_pre) >>
     pure_asm_rewrite_tac[] >> simp_tac bool_ss [] >>
     qexistsl [`initial`, `st.cs_next_var`, `32+32*word_size (maxlen+(case method_id of NONE => 0 | SOME mid => 4))`, `p`, `st.cs_next_id`, `w`] >>
     pure_asm_rewrite_tac[] >> simp_tac bool_ss [] >>
     rpt strip_tac >>
     qpat_x_assum `!inst b sz. _` (qspecl_then [`inst`, `b`, `sz`] mp_tac) >>
     asm_rewrite_tac[] >> simp_tac bool_ss []) >>
  drule_all compile_abi_encode_to_buf_window_strong_run >> strip_tac >>
  rename1 `window_strong_result ctx func ready body_end len at av d prepared body_state` >>
  `eval_operand (FST ops) body_state = SOME (n2w p)` by
    (irule abi_encode_setup_buffer_eval >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> first_assum ACCEPT_TAC) >>
  qpat_assum `window_strong_result _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE
      [window_strong_result_def, abi_encoder_window_result_def]) >>
  drule_all abi_encode_finish_reach_open >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `mem_bytes_at (p+32) m body_state.vs_memory = mem_bytes_at (p+32) m prepared.vs_memory` by
    (irule window_alloca_growth_frame >>
     qpat_assum `abi_builtin_encode_setup_frame _ _ _ _ _ _ _`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_builtin_encode_setup_frame_def]) >>
     conj_tac >- (qpat_x_assum `d + LENGTH _ <= _` mp_tac >>
       pure_asm_rewrite_tac[] >> decide_tac) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`window_alloca_sites func (frag_ids ready body_end)`, `[(d,LENGTH (enc at av))]`] >>
     reverse conj_tac >-
       (conj_tac >- (simp_tac (srw_ss()) [] >> first_assum ACCEPT_TAC) >>
        first_assum ACCEPT_TAC) >>
     qpat_x_assum `d = _` SUBST_ALL_TAC >>
     qpat_x_assum `outsz = _` SUBST_ALL_TAC >>
     qpat_x_assum `m = _` SUBST_ALL_TAC >>
     rpt strip_tac >>
     qpat_x_assum `_ IN window_alloca_sites _ _` mp_tac >>
     simp_tac (srw_ss()) [window_alloca_sites_def] >> strip_tac >>
     qpat_x_assum `!inst b sz. MEM inst _ /\ _ ==> _`
       (qspecl_then [`inst`, `b`, `sz`] mp_tac) >>
     qpat_x_assum `FLOOKUP prepared.vs_allocas i = SOME (b,sz)` mp_tac >>
     pure_asm_rewrite_tac[] >> simp_tac bool_ss []) >>
  `mem_bytes_at d (LENGTH (enc at av)) actual.vs_memory = enc at av` by
    (qpat_assum `abi_decode_frame p 32 body_state actual`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_decode_frame_def]) >>
     qpat_x_assum `!p' k. _` (qspecl_then [`d`, `LENGTH (enc at av)`] mp_tac) >>
     (impl_tac >- (qpat_x_assum `d = _` mp_tac >> decide_tac)) >>
     disch_then SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `(case method_id of NONE => T | SOME mid =>
      mem_bytes_at (p+32) 4 actual.vs_memory = abi_builtin_encode_method_bytes mid)` by
    (qpat_assum `abi_decode_frame p 32 body_state actual`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_decode_frame_def]) >>
     `mem_bytes_at (p+32) m actual.vs_memory = mem_bytes_at (p+32) m body_state.vs_memory` by
       (qpat_x_assum `!p' k. _` (qspecl_then [`p+32`, `m`] mp_tac) >>
        simp_tac bool_ss [arithmeticTheory.LE_REFL]) >>
     qpat_x_assum `mem_bytes_at (p+32) m body_state.vs_memory = _` mp_tac >>
     qpat_x_assum `mem_bytes_at (p+32) m actual.vs_memory = _` mp_tac >>
     qpat_x_assum `case method_id of NONE => T | SOME mid => _` mp_tac >>
     qpat_x_assum `m = _` mp_tac >>
     Cases_on `method_id` >> simp_tac (srw_ss()) [] >> metis_tac[]) >>
  `abi_decode_sim ctx func initial actual` by
    (irule abi_decode_sim_trans >> qexists `prepared` >>
     conj_tac >- first_assum ACCEPT_TAC >>
     irule abi_decode_sim_trans >> qexists `body_state` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  qexistsl [`prepared`, `body_state`, `actual`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem abi_encode_bridge_phases_open:
  abi_builtin_encode_setup method_id maxlen st = (ops,ready) /\
  compile_abi_encode_to_buf (SND ops) src ei ready = (len,body_end) /\
  abi_builtin_encode_finish (FST ops) len m body_end = ((),final) /\
  m = (case method_id of NONE => 0 | SOME mid => 4) /\
  w = (case method_id of NONE => 0 | SOME mid => 32) /\
  d = p+32+m /\ outsz = 32+32*word_size (maxlen+m) /\
  fn_has_code st ready obs /\ fn_has_code ready body_end obs /\
  fn_has_code body_end final obs /\ fn_inst_ids_distinct obs /\
  obs.fn_name = func.fn_name /\
  (!i. MEM i (fn_insts obs) /\ i.inst_opcode <> STOP /\
       i.inst_opcode <> NOP ==> MEM i (fn_insts func)) /\
  (!i. MEM i (fn_insts obs) ==> i.inst_opcode <> INVOKE) /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,outsz)) /\
  outsz < dimword (:256) /\ p < dimword (:256) /\
  (method_id <> NONE ==> p+32 < dimword (:256)) /\
  ready.cs_next_var <= limit_st.cs_next_var /\ body_end.cs_next_var <= limit_st.cs_next_var /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  abi_encoder_admissible ei /\ abi_encoder_window_input ei at av sb cap initial.vs_memory /\
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
  (!inst b sz. MEM inst (fn_insts obs) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids ready body_end /\
    FLOOKUP (abi_builtin_allocate_state st.cs_next_id outsz initial).vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\ venomMemDefs$regions_disjoint (sb,cap) (b,sz) /\
    venomMemDefs$regions_disjoint (d,LENGTH (enc at av)) (b,sz) /\
    venomMemDefs$regions_disjoint (p+32,m) (b,sz)) ==>
  ?prepared body actual.
    eval_operand (FST ops) actual = SOME (n2w p) /\
    mload p actual = n2w (LENGTH (enc at av)+m) /\
    mem_bytes_at d (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    (case method_id of NONE => T | SOME mid =>
      mem_bytes_at (p+32) 4 actual.vs_memory = abi_builtin_encode_method_bytes mid) /\
    ~actual.vs_halted /\ actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    abi_decode_sim ctx obs initial actual /\
    abi_builtin_encode_setup_frame st.cs_next_var st.cs_next_id outsz p w initial prepared /\
    window_strong_result (ctx with ctx_functions := [obs]) obs ready body_end len at av d prepared body /\
    abi_decode_frame p 32 body actual /\
    actual.vs_allocas = body.vs_allocas /\ actual.vs_alloca_next = body.vs_alloca_next /\
    abi_encoder_registered_effect {} [(p,32)] body actual /\
    (!op v. abi_decoder_operand_live body_end.cs_next_var op /\ eval_operand op body = SOME v ==>
      eval_operand op actual = SOME v)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `alloca_room (ctx with ctx_functions := [obs]) obs
     (abi_builtin_allocate_state st.cs_next_id outsz initial)` by
    (drule_all abi_encode_bridge_local_room >> simp_tac bool_ss []) >>
  drule_all abi_encode_window_phases_open >> strip_tac >>
  `abi_decode_sim ctx obs initial actual` by
    (drule_all abi_decode_sim_ctx_no_invoke >> simp_tac bool_ss []) >>
  qexistsl [`prepared`, `body'`, `actual`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem abi_encode_empty_region[local]:
  !q r. venomMemDefs$regions_disjoint (q,0) r
Proof
  rpt gen_tac >> Cases_on `r` >> simp[venomMemDefsTheory.regions_disjoint_def]
QED

Theorem abi_encode_window_none_phases_open:
  abi_builtin_encode_setup NONE maxlen st = (ops,ready) /\
  compile_abi_encode_to_buf (SND ops) src ei ready = (len,body_end) /\
  abi_builtin_encode_finish (FST ops) len 0 body_end = ((),final) /\
  outsz = 32+32*word_size maxlen /\
  fn_has_code st ready func /\ fn_has_code ready body_end func /\
  fn_has_code body_end final func /\ fn_inst_ids_distinct func /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,outsz)) /\
  outsz < dimword (:256) /\ p < dimword (:256) /\
  ready.cs_next_var <= limit_st.cs_next_var /\ body_end.cs_next_var <= limit_st.cs_next_var /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  abi_encoder_admissible ei /\ abi_encoder_window_input ei at av sb cap initial.vs_memory /\
  eval_operand src initial = SOME (n2w sb) /\ abi_decoder_operand_live st.cs_next_var src /\
  (!x. src = Var x \/ SND ops = Var x ==> not_fresh_at ready x) /\
  abi_decoder_operand_live body_end.cs_next_var (FST ops) /\
  alloca_inv (abi_builtin_allocate_state st.cs_next_id outsz initial) /\
  alloca_room ctx func (abi_builtin_allocate_state st.cs_next_id outsz initial) /\
  sb+cap <= (abi_builtin_allocate_state st.cs_next_id outsz initial).vs_alloca_next /\
  p+32+LENGTH (enc at av) <= (abi_builtin_allocate_state st.cs_next_id outsz initial).vs_alloca_next /\
  venomMemDefs$regions_disjoint (sb,cap) (p+32,LENGTH (enc at av)) /\
  (sb+cap <= p+32 \/ p+32 <= sb) /\
  (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids ready body_end /\
    FLOOKUP (abi_builtin_allocate_state st.cs_next_id outsz initial).vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\ venomMemDefs$regions_disjoint (sb,cap) (b,sz) /\
    venomMemDefs$regions_disjoint (p+32,LENGTH (enc at av)) (b,sz)) ==>
  ?prepared body actual.
    eval_operand (FST ops) actual = SOME (n2w p) /\
    mload p actual = n2w (LENGTH (enc at av)) /\
    mem_bytes_at (p+32) (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    ~actual.vs_halted /\ actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    abi_decode_sim ctx func initial actual /\
    abi_builtin_encode_setup_frame st.cs_next_var st.cs_next_id outsz p 0 initial prepared /\
    window_strong_result ctx func ready body_end len at av (p+32) prepared body /\
    abi_decode_frame p 32 body actual /\
    actual.vs_allocas = body.vs_allocas /\ actual.vs_alloca_next = body.vs_alloca_next /\
    abi_encoder_registered_effect {} [(p,32)] body actual /\
    (!op v. abi_decoder_operand_live body_end.cs_next_var op /\ eval_operand op body = SOME v ==>
      eval_operand op actual = SOME v)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encode_none_setup_buffer_old >> strip_tac >>
  qpat_x_assum `outsz = _` SUBST_ALL_TAC >>
  mp_tac (Q.INST [`method_id` |-> `NONE`, `m` |-> `0`, `w` |-> `0`, `d` |-> `p+32`,
        `outsz` |-> `32+32*word_size maxlen`]
      (SPEC_ALL abi_encode_window_phases_open)) >>
  (impl_tac >-
    (pure_asm_rewrite_tac [optionTheory.option_CLAUSES, arithmeticTheory.ADD_0,
       abi_encode_empty_region] >> simp_tac bool_ss [] >> first_assum ACCEPT_TAC)) >>
  pure_rewrite_tac [optionTheory.option_CLAUSES, arithmeticTheory.ADD_0] >>
  simp_tac bool_ss []
QED

Theorem abi_encode_window_some_phases_open:
  abi_builtin_encode_setup (SOME mid) maxlen st = (ops,ready) /\
  compile_abi_encode_to_buf (SND ops) src ei ready = (len,body_end) /\
  abi_builtin_encode_finish (FST ops) len 4 body_end = ((),final) /\
  outsz = 32+32*word_size (maxlen+4) /\
  fn_has_code st ready func /\ fn_has_code ready body_end func /\
  fn_has_code body_end final func /\ fn_inst_ids_distinct func /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,outsz)) /\
  outsz < dimword (:256) /\ p < dimword (:256) /\ p+32 < dimword (:256) /\
  ready.cs_next_var <= limit_st.cs_next_var /\ body_end.cs_next_var <= limit_st.cs_next_var /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  abi_encoder_admissible ei /\ abi_encoder_window_input ei at av sb cap initial.vs_memory /\
  eval_operand src initial = SOME (n2w sb) /\ abi_decoder_operand_live st.cs_next_var src /\
  (!x. src = Var x \/ SND ops = Var x ==> not_fresh_at ready x) /\
  (!x. FST ops = Var x ==> not_fresh_at ready x) /\
  abi_decoder_operand_live body_end.cs_next_var (FST ops) /\
  alloca_inv (abi_builtin_allocate_state st.cs_next_id outsz initial) /\
  alloca_room ctx func (abi_builtin_allocate_state st.cs_next_id outsz initial) /\
  sb+cap <= (abi_builtin_allocate_state st.cs_next_id outsz initial).vs_alloca_next /\
  p+36+LENGTH (enc at av) <= (abi_builtin_allocate_state st.cs_next_id outsz initial).vs_alloca_next /\
  venomMemDefs$regions_disjoint (sb,cap) (p+36,LENGTH (enc at av)) /\
  (sb+cap <= p+32 \/ p+64 <= sb) /\
  (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids ready body_end /\
    FLOOKUP (abi_builtin_allocate_state st.cs_next_id outsz initial).vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\ venomMemDefs$regions_disjoint (sb,cap) (b,sz) /\
    venomMemDefs$regions_disjoint (p+36,LENGTH (enc at av)) (b,sz) /\
    venomMemDefs$regions_disjoint (p+32,4) (b,sz)) ==>
  ?prepared body actual.
    eval_operand (FST ops) actual = SOME (n2w p) /\
    mload p actual = n2w (LENGTH (enc at av)+4) /\
    mem_bytes_at (p+36) (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    mem_bytes_at (p+32) 4 actual.vs_memory = abi_builtin_encode_method_bytes mid /\
    ~actual.vs_halted /\ actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    abi_decode_sim ctx func initial actual /\
    abi_builtin_encode_setup_frame st.cs_next_var st.cs_next_id outsz p 32 initial prepared /\
    window_strong_result ctx func ready body_end len at av (p+36) prepared body /\
    abi_decode_frame p 32 body actual /\
    actual.vs_allocas = body.vs_allocas /\ actual.vs_alloca_next = body.vs_alloca_next /\
    abi_encoder_registered_effect {} [(p,32)] body actual /\
    (!op v. abi_decoder_operand_live body_end.cs_next_var op /\ eval_operand op body = SOME v ==>
      eval_operand op actual = SOME v)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `outsz = _` SUBST_ALL_TAC >>
  `venomMemDefs$regions_disjoint (p+32,4) (p+36,LENGTH (enc at av))` by
    (simp_tac std_ss [venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `p+32+4 = p+36` by decide_tac >>
  `p+32+32 = p+64` by decide_tac >>
  mp_tac (Q.INST [`method_id` |-> `SOME mid`, `m` |-> `4`, `w` |-> `32`, `d` |-> `p+36`,
        `outsz` |-> `32+32*word_size (maxlen+4)`]
      (SPEC_ALL abi_encode_window_phases_open)) >>
  (impl_tac >-
    (pure_asm_rewrite_tac [optionTheory.option_CLAUSES] >>
     simp_tac bool_ss [] >> first_assum ACCEPT_TAC)) >>
  pure_rewrite_tac [optionTheory.option_CLAUSES] >> simp_tac bool_ss []
QED

(* Producer-facing view: resources remain explicit, while the encoded value
   is named by the producer's byte equality. *)
Theorem abi_encode_bridge_bytes_phases_open:
  enc at av = bytes /\
  abi_builtin_encode_setup method_id maxlen st = (ops,ready) /\
  compile_abi_encode_to_buf (SND ops) src ei ready = (len,body_end) /\
  abi_builtin_encode_finish (FST ops) len m body_end = ((),final) /\
  m = (case method_id of NONE => 0 | SOME mid => 4) /\
  w = (case method_id of NONE => 0 | SOME mid => 32) /\
  d = p+32+m /\ outsz = 32+32*word_size (maxlen+m) /\
  fn_has_code st ready obs /\ fn_has_code ready body_end obs /\
  fn_has_code body_end final obs /\ fn_inst_ids_distinct obs /\
  obs.fn_name = func.fn_name /\
  (!i. MEM i (fn_insts obs) /\ i.inst_opcode <> STOP /\
       i.inst_opcode <> NOP ==> MEM i (fn_insts func)) /\
  (!i. MEM i (fn_insts obs) ==> i.inst_opcode <> INVOKE) /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,outsz)) /\
  outsz < dimword (:256) /\ p < dimword (:256) /\
  (method_id <> NONE ==> p+32 < dimword (:256)) /\
  ready.cs_next_var <= limit_st.cs_next_var /\ body_end.cs_next_var <= limit_st.cs_next_var /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  abi_encoder_admissible ei /\ abi_encoder_window_input ei at av sb cap initial.vs_memory /\
  eval_operand src initial = SOME (n2w sb) /\ abi_decoder_operand_live st.cs_next_var src /\
  (!x. src = Var x \/ SND ops = Var x ==> not_fresh_at ready x) /\
  (!x. FST ops = Var x ==> not_fresh_at ready x) /\
  abi_decoder_operand_live body_end.cs_next_var (FST ops) /\
  alloca_inv (abi_builtin_allocate_state st.cs_next_id outsz initial) /\
  alloca_room ctx func (abi_builtin_allocate_state st.cs_next_id outsz initial) /\
  sb+cap <= (abi_builtin_allocate_state st.cs_next_id outsz initial).vs_alloca_next /\
  d+LENGTH bytes <= (abi_builtin_allocate_state st.cs_next_id outsz initial).vs_alloca_next /\
  venomMemDefs$regions_disjoint (sb,cap) (d,LENGTH bytes) /\
  (sb+cap <= p+32 \/ p+32+w <= sb) /\
  venomMemDefs$regions_disjoint (p+32,m) (d,LENGTH bytes) /\
  (!inst b sz. MEM inst (fn_insts obs) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids ready body_end /\
    FLOOKUP (abi_builtin_allocate_state st.cs_next_id outsz initial).vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\ venomMemDefs$regions_disjoint (sb,cap) (b,sz) /\
    venomMemDefs$regions_disjoint (d,LENGTH bytes) (b,sz) /\
    venomMemDefs$regions_disjoint (p+32,m) (b,sz)) ==>
  ?prepared body actual.
    eval_operand (FST ops) actual = SOME (n2w p) /\
    mload p actual = n2w (LENGTH bytes+m) /\
    mem_bytes_at (p+32+m) (LENGTH bytes) actual.vs_memory = bytes /\
    (case method_id of NONE => T | SOME mid =>
      mem_bytes_at (p+32) 4 actual.vs_memory = abi_builtin_encode_method_bytes mid) /\
    ~actual.vs_halted /\ actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    abi_decode_sim ctx obs initial actual /\
    abi_builtin_encode_setup_frame st.cs_next_var st.cs_next_id outsz p w initial prepared /\
    window_strong_result (ctx with ctx_functions := [obs]) obs ready body_end len at av d prepared body /\
    abi_decode_frame p 32 body actual /\
    actual.vs_allocas = body.vs_allocas /\ actual.vs_alloca_next = body.vs_alloca_next /\
    abi_encoder_registered_effect {} [(p,32)] body actual /\
    (!op v. abi_decoder_operand_live body_end.cs_next_var op /\ eval_operand op body = SOME v ==>
      eval_operand op actual = SOME v)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `enc at av = bytes` (SUBST_ALL_TAC o SYM) >>
  drule_all abi_encode_bridge_phases_open >>
  qpat_x_assum `d = _` SUBST_ALL_TAC >>
  simp_tac bool_ss []
QED
