(* Materialize the nonword at the actual slot returned by a linked Pop. *)
Theory bodyPopReadSlotBufferMods
Ancestors
  bodyIfExpArmUnwrapMods exprPtrUnwrapStorageLayout
  bodyFullPostsMods bodyFullShadowBodyInv bodyPtrDefs
  exprLowering exprSimMemDefs loweringPosts fragGasOriginPtr
  vyperStorageFootprint vyperInterpreter vyperAST context finite_map words

Theorem pop_nonword_slot_read_mods:
  compile_expr ce ty (Pop ann bt) sa = (LocatedValue ann p,sm) /\
  p.ptr_location = slot_loc tr /\ ~is_word_type ann /\
  unwrap_value ce (LocatedValue ann p) sm = (op,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  (!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  expr_body_pre_mods mods ce cx env (Pop ann bt) es /\
  eval_expr cx (Pop ann bt) (es with gas_obs := gs) = (INL tv,ee) /\
  read_result cx tv ee = (INL v,ee) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func ce cx (Pop ann bt) es sa sm s0 ee tv
      (LocatedValue ann p) s /\ ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  vv_store_bound cx (post_value_type ce (Pop ann bt))
    (lowered_value_type ce (Pop ann bt)) ee tv (LocatedValue ann p) s /\
  ptr_vv_ok cx (post_value_type ce (Pop ann bt)) tv (LocatedValue ann p) ee G tn s /\
  ghost_kept_at lo ce es sa Gi ti s0 G tn /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\ alloca_history func s ==>
  ?z Gf tf rt w.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gf,tf)) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      expr_post_mods H ctx func ce cx (Pop ann bt) es sa sb s0 ee v op z /\
      ghost_inv_at_mods (DF H) lo d ce cx ee Gf tf z) /\
    ghost_kept_at lo ce es sa Gi ti s0 Gf tf /\
    ptr_val_ok cx (post_value_type ce (Pop ann bt)) v op Gf tf z /\
    ptr_buf_ok ce (Pop ann bt) op Gf z /\
    expr_store_bound cx (post_value_type ce (Pop ann bt)) v op z /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func z /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\ s0.vs_alloca_next <= z.vs_alloca_next /\
    evaluate_type (get_tenv cx) ann = SOME rt /\
    type_memory_bytes ce (lowered_value_type ce (Pop ann bt)) = type_memory_size rt /\
    eval_operand op z = SOME w /\ op_taint tf op = {} /\
    (!mem. mem_agree_outside tf.t_mem z.vs_memory mem ==> val_in_memory rt v (w2n w) mem) /\
    FLOOKUP z.vs_allocas sm.cs_next_id = SOME (w2n w,type_memory_size rt) /\
    lo <= w2n w /\
    (type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
    (!aid ent. FLOOKUP s.vs_allocas aid = SOME ent ==> FLOOKUP z.vs_allocas aid = SOME ent) /\
    (!x cap. not_fresh_at sm x /\ ptr_covers G tn x s cap ==> ptr_covers Gf tf x z cap)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac unwrap_slot_ensure_layout >>
  `~is_word_type (expr_type (Pop ann bt))` by simp[expr_type_def] >>
  `slot_loc tr <> LocMemory /\ slot_loc tr <> LocCode` by
    (Cases_on `tr` >> simp[slot_loc_def]) >>
  mp_tac (Q.INST [`e` |-> `Pop ann bt`, `vv` |-> `LocatedValue ann p`,
                   `k` |-> `sm`] ifexp_arm_nonword_unwrap_mods) >>
  (impl_tac >- (asm_rewrite_tac[] >> simp[vv_location_def])) >>
  disch_then (qx_choosel_then [`val0`,`z`,`Gf`,`tf`,`pt`,`rt`,`w`]
    (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `(sb = sm /\ _) \/ _` strip_assume_tac
  >- fs[] >>
  `val0 = v` by fs[] >>
  qpat_x_assum `val0 = v` SUBST_ALL_TAC >>
  `lowered_value_type ce (Pop ann bt) = ann` by
    (qpat_assum `post_value_type ce (Pop ann bt) = _` mp_tac >>
     simp[NoAsms,post_value_type_def,expr_type_def] >> metis_tac[]) >>
  `evaluate_type (get_tenv cx) ann = SOME rt` by
    (qpat_assum `evaluate_type _ (lowered_value_type _ _) = SOME rt` mp_tac >>
     qpat_assum `lowered_value_type ce (Pop ann bt) = ann`
       (pure_once_rewrite_tac o single) >> disch_then ACCEPT_TAC) >>
  qexistsl [`z`,`Gf`,`tf`,`rt`,`w`] >>
  asm_rewrite_tac[] >> decide_tac
QED
