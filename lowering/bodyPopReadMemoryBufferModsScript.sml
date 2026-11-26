(* Nonword Pop reads reuse the buffer at the reached local place. *)
Theory bodyPopReadMemoryBufferMods
Ancestors
  bodyFullPostsMods exprSimMemoryPath exprSimUnwrapProps exprSimMemDefs
  loweringPosts bodyPtrDefs fragGasOriginPtr compileEnv valueCopyBytes

Theorem pop_buffer_local_post[local]:
  p.ptr_location = LocMemory /\
  vv_post_mods H ctx func ce cx e es sa sm s0 ee (PlaceR (MemoryPlace id path))
    (LocatedValue t p) s ==>
  vv_post H ctx func ce cx e es sa sm s0 ee (PlaceR (MemoryPlace id path))
    (LocatedValue t p) s /\ immutable_frame_mods func ce cx ee s
Proof
  strip_tac >>
  qpat_x_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[vv_post_mods_def, vv_holds_mods_def, vv_place_ptr_mods_def] >>
  strip_tac >> rewrite_tac[vv_post_def] >> rpt conj_tac >>
  (first_assum ACCEPT_TAC ORELSE simp[])
QED

Theorem pop_nonword_memory_read_mods:
  unwrap_value ce (LocatedValue t p) sm = (op,sb) /\
  p.ptr_location = LocMemory /\ ~is_word_type t /\
  read_result cx (PlaceR (MemoryPlace id path)) ee = (INL v,ee) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func ce cx (Pop ann bt) es sa sm s0 ee
      (PlaceR (MemoryPlace id path)) (LocatedValue t p) s /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  vv_store_bound cx (post_value_type ce (Pop ann bt))
    (lowered_value_type ce (Pop ann bt)) ee
    (PlaceR (MemoryPlace id path)) (LocatedValue t p) s /\
  ptr_vv_ok cx (post_value_type ce (Pop ann bt))
    (PlaceR (MemoryPlace id path)) (LocatedValue t p) ee G tn s /\
  ptr_buf_ok ce (Pop ann bt) p.ptr_operand G s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  alloca_history func s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  s0.vs_alloca_next <= s.vs_alloca_next /\ ghost_kept_at lo ce es sa G0 tn0 s0 G tn ==>
  ?u Gf tnf. !H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gf,tnf) /\
    expr_post_mods H ctx func ce cx (Pop ann bt) es sa sb s0 ee v op u /\
    expr_store_bound cx (post_value_type ce (Pop ann bt)) v op u /\
    u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    s0.vs_alloca_next <= u.vs_alloca_next /\
    ghost_inv_at_mods (DF H) lo d ce cx ee Gf tnf u /\
    ptr_val_ok cx (post_value_type ce (Pop ann bt)) v op Gf tnf u /\
    (~is_word_type (post_value_type ce (Pop ann bt)) ==> ptr_buf_ok ce (Pop ann bt) op Gf u) /\
    ghost_kept_at lo ce es sa G0 tn0 s0 Gf tnf
Proof
  strip_tac >>
  `op = p.ptr_operand /\ sb = sm` by
    (qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
     simp[unwrap_memory_compile, comp_return_def]) >>
  qexistsl [`s`,`G`,`tn`] >> gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  drule_all_then strip_assume_tac pop_buffer_local_post >>
  `~is_word_type (expr_type (Pop ann bt))` by
    (qpat_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [vv_post_def]) >>
     qpat_x_assum `vv_holds _ _ _ _ _ _ _` mp_tac >>
     simp[vv_holds_def] >> metis_tac[is_bytestring_word_type]) >>
  drule_all_then assume_tac vv_post_read_result >>
  simp[cj 1 gas_origin_ptr_path_rules, expr_post_mods_def] >>
  conj_tac
  >- (irule expr_post_of_vv_post_memory >> simp[] >> qexists_tac `t` >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `vv_store_bound _ _ _ _ _ _ _` mp_tac >>
      simp[vv_store_bound_def, expr_store_bound_def] >> metis_tac[]) >>
  qpat_x_assum `ptr_vv_ok _ _ _ _ _ _ _ _` mp_tac >>
  simp[ptr_vv_ok_def, ptr_val_ok_def]
QED
