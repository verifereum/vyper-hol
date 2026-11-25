(* Preserve the actual data window at the ordinary Slice capture cut. *)
Theory bodySliceDynamicCaptureMods
Ancestors
  bodyFullBuiltinSliceDynamicCapture
  bodyFullUnwrapRun stateRelProj list
  bodyForRangeScalarFrameMods bodyFullPostsMods bodyFullShadowBodyInv
  bodyPtrBytestringBuiltinsCalldataReserved exprSimHashBoundary
  exprSimWordArgs exprSimSliceCaptureControl abiEncodeOwnership
  logTopicFramePtr valueEncodingProofs valueEncodingDefs bodyFullHashKeccakFixed
  bodyMemoryDefs allocaHistory fragGasOriginPtr freshWrites
  loweringPosts exprLoweringProps loweringStateRelDefs bodyPtrDefs
  compileEnv ptrDiscipline supportedTypes vyperValue vyperTyping words venomState

Theorem slice_dynamic_input_mods[local]:
  expr_post (H:(bool # bytes32 # type_value) list # num list)
    ctx func ce cx e es0 sa sm s0 es v op s /\
  expr_type e = BaseT bt /\
  is_bytestring_type (BaseT bt) /\
  evaluate_type (get_tenv cx) (BaseT bt) = SOME tv /\ value_has_type tv v /\
  ptr_val_ok cx (BaseT bt) v op G tn s ==>
  ?x p bs. op = Var x /\ lookup_var x s = SOME p /\
    (v = BytesV bs \/ (?str. v = StringV str /\ bs = MAP (n2w o ORD) str)) /\
    mload (w2n p) s = n2w (LENGTH bs) /\
    mem_bytes_at (w2n p+32) (LENGTH bs) s.vs_memory = bs /\
    ptr_covers G tn x s (32+LENGTH bs) /\
    (!i. w2n p <= i /\ i < w2n p+32+LENGTH bs ==> i NOTIN tn.t_mem) /\
    w2n p+32+LENGTH bs <= s.vs_alloca_next /\
    w2n p+32+LENGTH bs < dimword (:256)
Proof
  strip_tac >>
  `?k. bt = BytesT (Dynamic k) \/ bt = StringT k` by
    (qpat_x_assum `is_bytestring_type _` mp_tac >>
     Cases_on `bt` >> simp[is_bytestring_type_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >> simp[is_bytestring_type_def]) >>
  `~is_word_type (BaseT bt) /\ supported_scalar_type (BaseT bt)` by
    gvs[is_word_type_def,supported_scalar_type_def,
        supported_word_type_def,supported_string_type_def] >>
  `post_value_type ce e = expr_type e` by
    (irule post_value_type_bytestring >> simp[is_bytestring_type_def]) >>
  `expr_val_rel cx (BaseT bt) v op s /\
   expr_val_at ce cx (BaseT bt) sa sm es v op s` by fs[expr_post_def] >>
  `?p. eval_operand op s = SOME p` by fs[expr_val_rel_def] >>
  drule_all_then assume_tac expr_val_rel_memory >>
  `?bs. (v = BytesV bs \/ (?str. v = StringV str /\ bs = MAP (n2w o ORD) str)) /\
    val_footprint tv v = 32+LENGTH bs /\
    mem_word_at (w2n p) s.vs_memory = n2w (LENGTH bs) /\
    mem_bytes_at (w2n p+32) (LENGTH bs) s.vs_memory = bs` by
    (Cases_on `v` >> gvs[evaluate_type_def,value_has_type_def,
         val_footprint_def,val_in_memory_def]) >>
  drule expr_post_state >> strip_tac >>
  drule stateRelProjTheory.stmt_state_rel_alloca_room >>
  disch_then (strip_assume_tac o MATCH_MP (SPEC_ALL alloca_room_next_lt)) >>
  `w2n p + 32 + LENGTH bs <= s.vs_alloca_next` by
    (drule_all abi_encode_owned_footprint_frontier >> decide_tac) >>
  `LENGTH bs < dimword (:256)` by decide_tac >>
  drule_all_then strip_assume_tac ptr_val_ok_log_bytestring_window >>
  qexistsl_tac [`src`,`p`,`bs`] >>
  gvs[eval_operand_def,mem_word_at_eq_mload_proof] >> decide_tac
QED

Theorem slice_dynamic_capture_source_run_mods:
  compile_bytestring_src op sm = ((limit,data),sc) /\
  fn_has_code sm sc func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sm /\ (!x. op = Var x ==> not_fresh_at sm x) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  return_buf_frame d ce sm s /\ alloca_history func s /\
  expr_type e = BaseT bt /\ is_bytestring_type (BaseT bt) /\
  evaluate_type (get_tenv cx) (BaseT bt) = SOME tv /\ value_has_type tv v /\
  ptr_val_ok cx (BaseT bt) v op G tn s /\
  storage_trace_domain cx st0 es.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    expr_post_mods H ctx func ce cx e es0 sa sm s0 es v op s /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx es G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?t G' tn' lp dp p bs.
    (?q raw. eval_operand op s = SOME q /\ p = q + 32w /\
       w2n p = w2n q + 32 /\ run_inst_seq (emitted_insts sm sc) s = OK raw /\
       t = (raw with vs_inst_idx := LENGTH sc.cs_current_insts)) /\
    (v = BytesV bs \/ (?str. v = StringV str /\ bs = MAP (n2w o ORD) str)) /\
    limit = Var lp /\ data = Var dp /\ not_fresh_at sc lp /\ not_fresh_at sc dp /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')) /\
    ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb /\
    t.vs_inst_idx = LENGTH sc.cs_current_insts /\ alloca_history func t /\
    eval_operand limit t = SOME (n2w (LENGTH bs)) /\
    op_taint tn' limit = {} /\ op_prov G' limit = NONE /\
    lookup_var dp t = SOME p /\ ptr_covers G' tn' dp t (LENGTH bs) /\
    w2n p + LENGTH bs < dimword (:256) /\ w2n p + LENGTH bs <= t.vs_alloca_next /\
    mem_bytes_at (w2n p) (LENGTH bs) t.vs_memory = bs /\
    (!i. w2n p <= i /\ i < w2n p+LENGTH bs ==> i NOTIN tn'.t_mem) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ tn'.t_mem = tn.t_mem /\
    (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    return_buf_frame d ce sc t /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func ce cx es t /\ immutable_frame_mods func ce cx es t /\
      storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx es G' tn' t)
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> _` (drule_then strip_assume_tac) >>
  fs[expr_post_mods_def] >>
  drule_all_then (qx_choosel_then [`x`,`p`,`bs`]
    (map_every assume_tac o CONJUNCTS)) slice_dynamic_input_mods >>
  qpat_x_assum `op = Var x` SUBST_ALL_TAC >>
  `not_fresh_at sm x` by metis_tac[] >>
  `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func ce cx es s` by
    (drule expr_post_state >> simp[]) >>
  drule_then assume_tac (SPEC_ALL stmt_state_rel_allocas_below_fmp) >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  `w2n p+32 < dimword (:256) /\ w2n p+32 <= s.vs_alloca_next` by decide_tac >>
  mp_tac (Q.INST [`sa` |-> `sm`,`sb` |-> `sc`,`src` |-> `x`,
                  `len` |-> `limit`,`capacity` |-> `32+LENGTH bs`]
    slice_dynamic_capture_full_run) >>
  impl_tac >- simp[] >>
  disch_then (qx_choosel_then [`u`,`G'`,`tn'`] (map_every assume_tac o CONJUNCTS)) >>
  drule_then strip_assume_tac slice_bytestring_src_control >>
  qabbrev_tac `t = u with vs_inst_idx := LENGTH sc.cs_current_insts` >>
  `alloca_history func t` by suspend "history" >>
  `return_buf_frame d ce sc t` by suspend "return" >>
  `w2n (p+32w) = w2n p+32` by (simp[w2n_add_2,w2n_n2w] >> decide_tac) >>
  `?lp dp. limit = Var lp /\ data = Var dp /\ not_fresh_at sc lp /\
          not_fresh_at sc dp /\ ptr_covers G' tn' dp u (LENGTH bs)` by
    (qpat_x_assum `!n. 32+n <= _ ==> _` (qspec_then `LENGTH bs` mp_tac) >>
     simp[] >> strip_tac >>
     qpat_x_assum `?l r. limit = Var l /\ _` strip_assume_tac >>
     gvs[]) >>
  qexistsl_tac [`t`,`G'`,`tn'`,`lp`,`dp`,`p+32w`,`bs`] >>
  conj_tac >- (qexistsl_tac [`p`,`u`] >> fs[Abbr `t`,eval_operand_def]) >>
  suspend "finish"
QED

Resume slice_dynamic_capture_source_run_mods[history]:
  qunabbrev_tac `t` >> irule emitted_alloca_history >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`emitted_insts sm sc`,`s`,`sm`] >> simp[] >>
  conj_tac >- drule_then (ACCEPT_TAC o cj 2) stmt_state_rel_local_ptrs_alloca >>
  drule slice_bytestring_src_zero_code >> simp[EVERY_MEM]
QED

Resume slice_dynamic_capture_source_run_mods[return]:
  irule return_buf_frame_frame >>
  qexistsl_tac [`ce`,`s`,`sm`] >>
  `ci_mono sm sc` by
    (qspec_then `sm` mp_tac (Q.SPEC `Var x` ci_mono_compile_bytestring_src) >> fs[]) >>
  fs[ci_mono_def,Abbr `t`,lookup_var_def] >>
  rpt strip_tac >>
  qpat_assum `u = s with vs_vars := _` (mp_tac o AP_TERM ``\z. z.vs_alloca_next``) >> simp[]
QED

Resume slice_dynamic_capture_source_run_mods[finish]:
  `!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s /\
    FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)` by
    (qsuff_tac `!x. lookup_var x t = lookup_var x u` >- metis_tac[] >>
     simp[Abbr `t`,lookup_var_def]) >>
  qpat_assum `u = s with vs_vars := _`
    (strip_assume_tac o PURE_REWRITE_RULE [venom_state_component_equality,
      venom_state_accfupds]) >>
  simp[Abbr `t`,eval_operand_def,lookup_var_def,ptr_covers_def] >>
  suspend "finish_reduced"
QED

Resume slice_dynamic_capture_source_run_mods[finish_reduced]:
  conj_tac >- fs[eval_operand_def,lookup_var_def] >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> _` (drule_then strip_assume_tac) >>
  `stmt_state_rel H ctx func ce cx es u` by
    (irule stmt_state_rel_reserved_vars_update >> qexistsl_tac [`s`,`sm`] >>
     simp[] >> drule expr_post_state >> simp[] >> metis_tac[]) >>
  conj_tac >- simp[stmt_state_rel_inst_idx] >>
  conj_tac
  >- (irule immutable_frame_mods_exterior_frame >>
      qexistsl_tac [`es`,`s`,`sm`] >> simp[lookup_var_def] >> metis_tac[lookup_var_def]) >>
  irule ghost_inv_at_mods_exterior_frame >>
  qexistsl_tac [`G`,`es`,`s`,`sm`,`tn`] >> simp[lookup_var_def] >> metis_tac[lookup_var_def]
QED

Finalise slice_dynamic_capture_source_run_mods

Theorem slice_dynamic_capture_source_mods:
  compile_bytestring_src op sm = ((limit,data),sc) /\
  fn_has_code sm sc func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sm /\ (!x. op = Var x ==> not_fresh_at sm x) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  return_buf_frame d ce sm s /\ alloca_history func s /\
  expr_type e = BaseT bt /\ is_bytestring_type (BaseT bt) /\
  evaluate_type (get_tenv cx) (BaseT bt) = SOME tv /\ value_has_type tv v /\
  ptr_val_ok cx (BaseT bt) v op G tn s /\
  storage_trace_domain cx st0 es.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    expr_post_mods H ctx func ce cx e es0 sa sm s0 es v op s /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx es G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?t G' tn' lp dp p bs.
    (v = BytesV bs \/ (?str. v = StringV str /\ bs = MAP (n2w o ORD) str)) /\
    limit = Var lp /\ data = Var dp /\ not_fresh_at sc lp /\ not_fresh_at sc dp /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')) /\
    ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb /\
    t.vs_inst_idx = LENGTH sc.cs_current_insts /\ alloca_history func t /\
    eval_operand limit t = SOME (n2w (LENGTH bs)) /\
    op_taint tn' limit = {} /\ op_prov G' limit = NONE /\
    lookup_var dp t = SOME p /\ ptr_covers G' tn' dp t (LENGTH bs) /\
    w2n p + LENGTH bs < dimword (:256) /\ w2n p + LENGTH bs <= t.vs_alloca_next /\
    mem_bytes_at (w2n p) (LENGTH bs) t.vs_memory = bs /\
    (!i. w2n p <= i /\ i < w2n p+LENGTH bs ==> i NOTIN tn'.t_mem) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ tn'.t_mem = tn.t_mem /\
    (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    return_buf_frame d ce sc t /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func ce cx es t /\ immutable_frame_mods func ce cx es t /\
      storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx es G' tn' t)
Proof
  disch_then (mp_tac o MATCH_MP (SPEC_ALL slice_dynamic_capture_source_run_mods)) >>
  disch_then (qx_choosel_then [`t`,`G'`,`tn'`,`lp`,`dp`,`p`,`bs`]
    (assume_tac o CONJUNCT2)) >>
  qexistsl_tac [`t`,`G'`,`tn'`,`lp`,`dp`,`p`,`bs`] >> first_assum ACCEPT_TAC
QED
