(* Store a fixed Slice source word in its registered staging window. *)
Theory bodySliceFixedStoreMods
Ancestors
  bodyFullBuiltinBytestringCopy wordLoadStorePtr bodyIfExpTypedGhostMods
  bodyIfExpTypedImmFrameMods bodyPtrMakeArrayCopyStateFrame bodyFullPostsMods
  bodyMemoryDefs stateRelProj allocaHistory fragGasOriginPtr emitHelperProps
  exprLoweringProps valueEncodingProps venomMemProps exprSimStorageCopy
  loweringStateRelDefs typedMemoryCopy assignTuplePtrCopyLen fragExec
  venomState venomInst ptrDiscipline words list pred_set

Theorem slice_fixed_store_history[local]:
  emit_void MSTORE [Var root;src] sm = ((),sb) /\ fn_has_code sm sb func /\
  alloca_history func u /\ u.vs_current_bb = sm.cs_current_bb /\
  u.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  alloca_history func (mstore a w u with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  drule emit_void_same_blocks >> strip_tac >>
  `LENGTH sb.cs_current_insts = SUC u.vs_inst_idx /\
   sb.cs_current_bb = sm.cs_current_bb` by fs[same_blocks_def] >>
  `alloca_history func (u with vs_inst_idx := SUC u.vs_inst_idx)` by
    (drule_all fn_has_code_same_block >> strip_tac >>
     qabbrev_tac `i = mk_inst sm.cs_next_id MSTORE [Var root;src] []` >>
     `get_instruction bb u.vs_inst_idx = SOME i` by
       (first_x_assum (qspec_then `0` mp_tac) >> simp[Abbr `i`]) >>
     irule history_nonalloca_advance >> conj_tac
     >- (qexistsl_tac [`bb`,`i`] >> simp[Abbr `i`,mk_inst_def]) >>
     first_assum ACCEPT_TAC) >>
  irule alloca_history_frame >>
  qexists_tac `u with vs_inst_idx := SUC u.vs_inst_idx` >>
  simp[mstore_def]
QED

Theorem slice_fixed_store_state_frame[local]:
  typed_copy_state_frame sm a 32 u (mstore a w u with vs_inst_idx := idx)
Proof
  simp[typed_copy_state_frame_def] >> conj_tac
  >- simp[mstore_def] >>
  conj_tac >- simp[mstore_def,lookup_var_def] >>
  simp[typed_copy_frame_def,mstore_memory_nondecreasing] >>
  rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >> simp[]
QED

Theorem slice_fixed_capture_store_mods:
  emit_void MSTORE [Var root;src] sm = ((),sb) /\ fn_has_code sm sb func /\
  local_ptrs_reserved ce sm /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  return_buf_frame d ce sm u /\ alloca_history func u /\
  lookup_var root u = SOME p /\ ptr_covers G tn root u 32 /\ not_fresh_at sm root /\
  eval_operand src u = SOME w /\ op_taint tn src = {} /\
  MEM (mk_inst aid ALLOCA [Lit 32w] [root]) (fn_insts func) /\
  FLOOKUP u.vs_allocas aid = SOME (w2n p,32) /\
  w2n p+32 < dimword (:256) /\ w2n p+32 <= u.vs_alloca_next /\
  (!name b len. local_region ce es.scopes u name b len ==>
    regions_disjoint (w2n p) 32 b len) /\
  lo <= w2n p /\ allocas_from lo u /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  ~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb /\
  u.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func ce cx es u /\ immutable_frame_mods func ce cx es u /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx es G tn u) ==>
  ?t G' tn'.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,G,tn) [] (OK t,G',tn')) /\
    t = (mstore (w2n p) w u with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func t /\
    not_fresh_at sb root /\ lookup_var root t = SOME p /\ ptr_covers G' tn' root t 32 /\
    w2n p+32 < dimword (:256) /\ w2n p+32 <= t.vs_alloca_next /\
    mem_bytes_at (w2n p) 32 t.vs_memory = word_to_bytes w T /\
    (!i. w2n p <= i /\ i < w2n p+32 ==> i NOTIN tn'.t_mem) /\
    t.vs_allocas = u.vs_allocas /\ t.vs_alloca_next = u.vs_alloca_next /\
    allocas_from lo t /\
    (!a len. a+len <= w2n p \/ w2n p+32 <= a ==>
      mem_bytes_at a len t.vs_memory = mem_bytes_at a len u.vs_memory) /\
    tn'.t_mem SUBSET tn.t_mem /\
    (!i. ~(w2n p <= i /\ i < w2n p+32) ==> (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x u /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    return_buf_frame d ce sb t /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func ce cx es t /\ immutable_frame_mods func ce cx es t /\
      storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx es G' tn' t)
Proof
  strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  drule emit_void_same_blocks >> strip_tac >>
  `LENGTH sb.cs_current_insts = SUC u.vs_inst_idx /\
   sb.cs_current_bb = sm.cs_current_bb` by fs[same_blocks_def] >>
  qabbrev_tac `i = mk_inst sm.cs_next_id MSTORE [Var root;src] []` >>
  qabbrev_tac `t = mstore (w2n p) w u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  qabbrev_tac `tf = step_taint i u (mstore (w2n p) w u) tn` >>
  `step_prov PG G i (mstore (w2n p) w u) = G /\
   tf.t_var = tn.t_var /\ tf.t_stor = tn.t_stor /\
   tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm` by
    simp[Abbr `i`,Abbr `tf`,ifexp_materialize_mstore_ghost] >>
  `tf.t_mem = tn.t_mem DIFF {j | w2n p <= j /\ j < w2n p+32}` by
    (simp[Abbr `i`,Abbr `tf`] >>
     simp[ifexp_materialize_mstore_taint,eval_operand_def]) >>
  `~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
   t.vs_inst_idx = LENGTH sb.cs_current_insts /\
   t.vs_allocas = u.vs_allocas /\ t.vs_alloca_next = u.vs_alloca_next /\
   t.vs_vars = u.vs_vars` by simp[Abbr `t`, mstore_def] >>
  `alloca_history func t` by
    (qunabbrev_tac `t` >> irule slice_fixed_store_history >> conj_tac
     >- first_assum ACCEPT_TAC >> qexistsl_tac [`root`,`sm`,`src`] >> simp[]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,G,tn) [] (OK t,G,tf)` by
    suspend "path" >>
  `typed_copy_state_frame sm (w2n p) 32 u t` by
    simp[Abbr `t`,slice_fixed_store_state_frame] >>
  `return_buf_frame d ce sb t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`ce`,`u`,`sm`] >>
     simp[lookup_var_def]) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func ce cx es t /\ immutable_frame_mods func ce cx es t /\
      storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx es G tf t` by
    suspend "horizon" >>
  qexistsl_tac [`t`,`G`,`tf`] >> suspend "finish"
QED

Resume slice_fixed_capture_store_mods[path]:
  gen_tac >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (u,G,tn) [] (OK t,G,tf)` by
    (drule_all bytestring_length_store_origin_edge >>
     simp[Abbr `t`,Abbr `tf`,Abbr `i`,ifexp_materialize_mstore_ghost]) >>
  metis_tac[gas_origin_ptr_path_rules,APPEND_NIL]
QED

Resume slice_fixed_capture_store_mods[horizon]:
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> _` (drule_then strip_assume_tac) >>
  conj_tac >- suspend "state" >>
  conj_tac
  >- (irule ifexp_typed_immutable_frame_mods >>
      qexistsl_tac [`w2n p`,`mk_inst aid ALLOCA [Lit 32w] [root]`,`sm`,`32`,`u`] >>
      simp[mk_inst_def]) >>
  simp[] >> irule ifexp_typed_copy_ghost_mods >>
  qexistsl_tac [`G`,`w2n p`,`func`,`sm`,`32`,`u`,`tn`] >> simp[op_taint_def] >>
  conj_tac
  >- (rpt gen_tac >> disch_tac >>
      qpat_assum `!name b len. local_region _ _ _ _ _ _ ==> _`
        (drule_then ACCEPT_TAC)) >>
  drule_then (ACCEPT_TAC o cj 1) stmt_state_rel_local_ptrs_alloca
QED

Resume slice_fixed_capture_store_mods[state]:
  irule literal_copy_window_stmt_state_rel >>
  qexistsl_tac [`aid`,`w2n p`,`32`,`root`,`sm`,`sm`,`u`] >>
  simp[lookup_var_def] >>
  `copy_static t = copy_static u` by simp[Abbr `t`,copy_static_def,mstore_def] >>
  fs[typed_copy_state_frame_def,typed_copy_frame_def] >>
  conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC
QED

Resume slice_fixed_capture_store_mods[finish]:
  `ptr_covers G tf root t 32` by
    (irule ptr_covers_lookup_frame >> qexistsl_tac [`G`,`u`,`tn`] >>
     fs[lookup_var_def,op_taint_def]) >>
  `mem_bytes_at (w2n p) 32 t.vs_memory = word_to_bytes w T` by
    simp[Abbr `t`,mem_bytes_at_mstore_same] >>
  `not_fresh_at sb root` by fs[not_fresh_at_def] >>
  `lookup_var root t = SOME p` by fs[lookup_var_def] >>
  `allocas_from lo t` by
    (simp[allocas_from_def] >>
     qpat_assum `allocas_from lo u` (ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
  qpat_assum `typed_copy_state_frame _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [typed_copy_state_frame_def,typed_copy_frame_def]) >>
  `!x. lookup_var x t = lookup_var x u` by simp[lookup_var_def] >>
  simp[op_taint_def,SUBSET_DEF] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> stmt_state_rel _ _ _ _ _ _ t /\ _`
    (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC
QED

Finalise slice_fixed_capture_store_mods
