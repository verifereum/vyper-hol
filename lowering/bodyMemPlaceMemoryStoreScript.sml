(* Counted writes of empty values into computed memory places. *)
Theory bodyMemPlaceMemoryStore
Ancestors
  augAssignPlaceWordStoreMemory placeStore stmtLowering loweringPosts
  bodyDeclMemoryCore exprSimProps exprLoweringProps fragGasMode venomState
  bodyMemPlaceDirectStore bodyMemPlaceStagedStore placeMemoryStateRebuild
  placeMemoryAssignForward placeMemoryLiveRegion

Theorem place_store_empty_memory_run_mem:
  compile_store_at_loc imm dst_op (Lit 0w) (SOME LocMemory) sa = ((),sb) /\
  eval_operand dst_op s = SOME w /\
  place_ptr_rel cenv cx s (PlaceR p) w (SOME LocMemory) (Type dty) /\
  (!x. dst_op = Var x ==> not_fresh_at sa x) /\
  has_length_word dty /\ evaluate_type (get_tenv cx) dty = SOME dtv /\
  expr_sim_inv cenv cx env ee /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  local_ptrs_reserved cenv sa /\ storage_place_region cx p /\
  (!id path entry t0.
    p = MemoryPlace id path /\ lookup_scopes id ee.scopes = SOME entry /\
    cenv.ce_var_type id = SOME t0 ==>
    evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
  stmt_state_rel ctx func cenv cx ee s /\
  write_place cx p (default_value dtv) ee = (INL (),ff) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  alloca_history func s /\ alloca_inv s /\
  w2n w + 32 <= s.vs_alloca_next ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
    stmt_state_rel ctx func cenv cx ff t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
      FLOOKUP t.vs_allocas aid = SOME b) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ s.vs_alloca_next = t.vs_alloca_next
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx ff (mstore (w2n w) 0w s)` by
    (Cases_on `p`
     >- (gvs[place_ptr_rel_def, slot_loc_def] >> Cases_on `b` >> gvs[])
     >- (irule place_store_empty_memory_state >>
     goal_assum (drule_at (Pat `expr_sim_inv _ _ _ _`)) >>
     goal_assum (drule_at (Pat `place_ptr_rel _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `evaluate_type _ dty = _`)) >> simp[]) >>
     gvs[place_ptr_rel_def]) >>
  `emit_void MSTORE [dst_op; Lit 0w] sa = ((),sb)` by
    gvs[compile_store_at_loc_def] >>
  `gas_marked_path T ctx func s 0
     (OK ((mstore (w2n w) 0w s) with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
   alloca_history func
     ((mstore (w2n w) 0w s) with vs_inst_idx := LENGTH sb.cs_current_insts) /\
   (!x. lookup_var x (mstore (w2n w) 0w s) = lookup_var x s) /\
   (mstore (w2n w) 0w s).vs_allocas = s.vs_allocas /\
   (mstore (w2n w) 0w s).vs_alloca_next = s.vs_alloca_next /\
   ~(mstore (w2n w) 0w s).vs_halted /\
   (mstore (w2n w) 0w s).vs_current_bb = sb.cs_current_bb` by
    (irule place_store_emit_run_mem >> simp[] >>
     qexistsl_tac [`dst_op`, `LocMemory`, `Lit 0w`, `sa`] >>
     simp[eval_operand_def]) >>
  qexists_tac `(mstore (w2n w) 0w s) with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  fs[stmt_state_rel_inst_idx, lookup_var_def]
QED

(* Restore at the execution endpoint, using the global outside-destination frame.
   r is s for a direct store, or the post-allocation state for a staged store. *)
Theorem place_store_endpoint_stmt_state[local]:
  stmt_state_rel ctx func cenv cx ee s /\
  stmt_state_rel ctx func cenv cx ee r /\
  expr_sim_inv cenv cx env ee /\ local_ptrs_reserved cenv sa /\
  place_ptr_rel cenv cx s (PlaceR p) w (SOME LocMemory) (Type dty) /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\ value_has_type dtv v /\
  write_place cx p v ee = (INL (),ff) /\
  (!id path entry t0. p = MemoryPlace id path /\
    lookup_scopes id ee.scopes = SOME entry /\ cenv.ce_var_type id = SOME t0 ==>
    evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
  val_in_memory dtv v (w2n w) t.vs_memory /\
  (t with <|vs_vars := r.vs_vars; vs_memory := r.vs_memory;
    vs_prev_bb := r.vs_prev_bb; vs_current_bb := r.vs_current_bb;
    vs_inst_idx := r.vs_inst_idx|>) = r /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  (!name b len. local_region cenv ee.scopes s name b len ==>
    local_region cenv ee.scopes r name b len) /\
  (!a n. a+n <= w2n w \/ w2n w+type_memory_size dtv <= a ==>
    mem_bytes_at a n t.vs_memory = mem_bytes_at a n r.vs_memory) ==>
  stmt_state_rel ctx func cenv cx ff t
Proof
  strip_tac >>
  drule_all memory_place_live_region >> strip_tac >>
  `local_region cenv ee.scopes r name b len` by metis_tac[] >>
  `immutable_alloca_sep func cenv cx ee r` by
    metis_tac[stmt_state_rel_def] >>
  irule memory_place_write_stmt_state >>
  goal_assum (drule_at (Pat `place_ptr_rel _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ r`)) >>
  goal_assum (drule_at (Pat `evaluate_type _ _ = _`)) >> simp[] >>
  qexistsl_tac [`env`, `sa`, `v`] >> simp[] >>
  conj_tac >- metis_tac[arithmeticTheory.ADD_COMM] >> rpt strip_tac >>
  `off + type_memory_size tv <= w2n w \/
    w2n w + type_memory_size dtv <= off` by
    (irule immutable_local_slice_disjoint >>
     goal_assum (drule_at (Pat `local_region _ _ r _ _ _`)) >>
     simp[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem place_store_direct_memory_cont:
  ~is_word_type dty /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  (!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
    type_memory_bytes cenv ty = type_memory_size tv) /\
  type_widens_to (get_tenv cx) sty dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  val_footprint dtv v <= type_memory_size dtv /\
  compile_store_memory cenv src dst dty sty sa = ((),sb) /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  w2n sw + type_memory_size stv <= s.vs_alloca_next /\
  w2n dw + type_memory_size dtv <= s.vs_alloca_next /\
  w2n sw + type_memory_size stv < dimword(:256) /\
  w2n dw + type_memory_size dtv < dimword(:256) /\
  (w2n sw + type_memory_size stv <= w2n dw \/
    w2n dw + type_memory_size dtv <= w2n sw) /\
  (emitted_blocks sa sb <> [] ==>
    ?bb. lookup_block sb.cs_current_bb func.fn_blocks = SOME bb /\
      phi_prefix_length bb.bb_instructions = 0) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  (!x. dst = Var x \/ src = Var x ==> not_fresh_at sa x) /\
  alloca_history func s /\ stmt_state_rel ctx func cenv cx ee s /\
  expr_sim_inv cenv cx env ee /\ local_ptrs_reserved cenv sa /\
  place_ptr_rel cenv cx s (PlaceR p) dw (SOME LocMemory) (Type dty) /\
  write_place cx p v ee = (INL (),ff) /\
  (!id path entry t0. p = MemoryPlace id path /\
    lookup_scopes id ee.scopes = SOME entry /\ cenv.ce_var_type id = SOME t0 ==>
    evaluate_type (get_tenv cx) t0 = SOME entry.type) ==>
  ?t. mem_cont_sim ctx func s t /\ stmt_state_rel ctx func cenv cx ff t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    alloca_inv t /\ alloca_room ctx func t /\ alloca_history func t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `alloca_inv s /\ alloca_room ctx func s` by fs[stmt_state_rel_def] >>
  drule_all place_direct_store_cont >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  `stmt_state_rel ctx func cenv cx ff t` by
    (irule place_store_endpoint_stmt_state >>
     goal_assum (drule_at (Pat `place_ptr_rel _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `evaluate_type _ _ = SOME dtv`)) >>
     goal_assum (drule_at (Pat `write_place _ _ _ _ = _`)) >>
     qexistsl_tac [`dtv`, `env`, `s`, `sa`] >> simp[] >>
     conj_tac >- metis_tac[arithmeticTheory.ADD_COMM] >>
     qpat_x_assum `_ = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  qexists_tac `t` >> simp[]
QED

Theorem place_store_staged_memory_cont:
  ~is_word_type dty /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  (!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
    type_memory_bytes cenv ty = type_memory_size tv) /\
  type_widens_to (get_tenv cx) sty dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  val_footprint stv v <= type_memory_size stv /\
  val_footprint dtv v <= type_memory_size dtv /\
  compile_alloc_buffer (type_memory_size stv) sa = (buf,sm) /\
  compile_copy_memory buf.buf_operand src (type_memory_size stv) sm = ((),sn) /\
  compile_store_memory cenv buf.buf_operand dst dty sty sn = ((),sb) /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  w2n sw + type_memory_size stv <= s.vs_alloca_next /\
  w2n dw + type_memory_size dtv <= s.vs_alloca_next /\
  type_memory_size stv < dimword(:256) /\
  w2n dw + type_memory_size dtv < dimword(:256) /\
  (emitted_blocks sn sb <> [] ==>
    ?bb. lookup_block sb.cs_current_bb func.fn_blocks = SOME bb /\
      phi_prefix_length bb.bb_instructions = 0) /\
  fn_has_code sa sn func /\ fn_has_code sn sb func /\
  fn_inst_ids_distinct func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  alloca_history func s /\ stmt_state_rel ctx func cenv cx ee s /\
  expr_sim_inv cenv cx env ee /\ local_ptrs_reserved cenv sa /\
  place_ptr_rel cenv cx s (PlaceR p) dw (SOME LocMemory) (Type dty) /\
  write_place cx p v ee = (INL (),ff) /\
  (!id path entry t0. p = MemoryPlace id path /\
    lookup_scopes id ee.scopes = SOME entry /\ cenv.ce_var_type id = SOME t0 ==>
    evaluate_type (get_tenv cx) t0 = SOME entry.type) ==>
  ?t. mem_cont_sim ctx func s t /\ stmt_state_rel ctx func cenv cx ff t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid r. FLOOKUP s.vs_allocas aid = SOME r ==> FLOOKUP t.vs_allocas aid = SOME r) /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    alloca_inv t /\ alloca_room ctx func t /\ alloca_history func t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all memory_place_live_region >> strip_tac >>
  drule (SIMP_RULE bool_ss [LET_THM] place_staged_store_cont) >>
  disch_then drule >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `val_in_memory _ _ _ _`)) >>
  disch_then (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
  disch_then (fn th => qpat_assum `eval_operand dst s = SOME dw`
    (mp_then (Pat `eval_operand _ _ = _`) mp_tac th)) >>
  disch_then (qspecl_then [`sb`, `type_memory_size dtv`, `dtv`] mp_tac) >>
  simp[] >>
  (impl_tac >- (rpt strip_tac >>
    `alloca_inv u /\ alloca_room ctx func u` by fs[stmt_state_rel_def] >>
    drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`) place_direct_store_cont >>
    disch_then (drule_at (Pat `val_in_memory _ _ _ _`)) >>
    disch_then (drule_at (Pat `evaluate_type _ dty = _`)) >>
    disch_then (drule_at (Pat `fn_has_code sn sb _`)) >>
    disch_then (drule_at (Pat `alloca_room _ _ u`)) >>
    simp[arithmeticTheory.ADD_COMM] >>
    (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
    disch_then (qx_choose_then `t` strip_assume_tac) >>
    qexists_tac `t` >> simp[] >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `u` (qx_choose_then `tw`
    (qx_choose_then `t` (map_every assume_tac o CONJUNCTS)))) >>
  `stmt_state_rel ctx func cenv cx ff t` by
    (irule place_store_endpoint_stmt_state >>
     goal_assum (drule_at (Pat `place_ptr_rel _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `evaluate_type _ _ = SOME dtv`)) >>
     goal_assum (drule_at (Pat `write_place _ _ _ _ = _`)) >>
     qexistsl_tac [`dtv`, `env`, `u`, `sa`] >>
     simp[] >> metis_tac[arithmeticTheory.ADD_SYM]) >>
  qexists_tac `t` >> simp[]
QED
