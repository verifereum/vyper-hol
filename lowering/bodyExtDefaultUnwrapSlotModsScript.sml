(* Unwrap an already reached storage/transient aggregate at the actual copy cursor. *)
Theory bodyExtDefaultUnwrapSlotMods
Ancestors
  bodyCopySlotRhsEndpointMods bodyCopyMaterializedRhsPostMods
  exprPtrUnwrapStorageShape exprOperandVar exprLoweringProps
  bodyFullPostsMods bodyFullShadowBodyInv bodyFullHashKeccakFixed
  fragGasOriginPtr fragGasPathPtr fragGasPathFrameMem
  loweringPosts loweringStateRelDefs bodyPtrDefs ptrDiscipline
  freshWrites compileEnv exprLowering exprSimProps vyperTyping
  vyperTypeStatePreservation vyperStorageTrace vyperStorageFootprint stateRelProj
  context finite_map words arithmetic

Theorem default_slot_reached_read[local]:
  vv_post_mods H ctx func ce cx e es sa sn s0 ee tv (LocatedValue tag p) s /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt ==>
  tag = post_value_type ce e /\
  ?v. read_result cx tv ee = (INL v,ee) /\ value_has_type rt v
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `p.ptr_location = slot_loc (p.ptr_location = LocTransient)` by
    (qpat_assum `p.ptr_location = LocStorage \/ _` strip_assume_tac >> simp[slot_loc_def]) >>
  `tag = post_value_type ce e /\
   ?key. eval_operand p.ptr_operand s = SOME key /\
     storage_holds cx (p.ptr_location = LocTransient) tag tv key ee s` by
    (qpat_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     Cases_on `p.ptr_location` >> gvs[vv_post_mods_def,vv_holds_mods_def,vv_holds_def]) >>
  qpat_x_assum `tag = _` SUBST_ALL_TAC >> simp[] >>
  qpat_x_assum `storage_holds _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [storage_holds_def]) >> gvs[] >>
  drule_then assume_tac (cj 1 evaluate_type_well_formed) >>
  drule_all_then assume_tac read_storage_slot_success_type >> asm_rewrite_tac[]
QED

Theorem default_unwrap_slot_prefix_mods:
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  ~is_word_type (post_value_type ce e) /\
  compile_expr ce ty e sa = (LocatedValue tag p,sm) /\
  unwrap_value ce (LocatedValue tag p) sn = (op,sc) /\
  sm.cs_next_var <= sn.cs_next_var /\ sm.cs_next_id <= sn.cs_next_id /\
  fn_has_code sn sc func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  (!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
  type_memory_bytes ce (post_value_type ce e) = type_memory_size rt /\
  type_memory_size rt < 2**64 /\ storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func ce cx e es sa sn s0 ee tv (LocatedValue tag p) s /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  ptr_vv_ok cx (post_value_type ce e) tv (LocatedValue tag p) ee G tn s /\
  ghost_kept_at lo ce es sa Gi ti s0 G tn /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sn.cs_current_bb /\
  s.vs_inst_idx = LENGTH sn.cs_current_insts /\ alloca_history func s ==>
  ?v z Gf tf w root.
    read_result cx tv ee = (INL v,ee) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gf,tf)) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      expr_post_mods H ctx func ce cx e es sa sc s0 ee v op z /\
      ghost_inv_at_mods (DF H) lo d ce cx ee Gf tf z) /\
    ghost_kept_at lo ce es sa Gi ti s0 Gf tf /\
    wb_frame ce ee ee sn s z /\ ghost_kept_at lo ce ee sn G tn s Gf tf /\
    (!x. not_fresh_at sn x ==> lookup_var x z = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP z.vs_allocas aid = SOME b) /\
    (!x cap. not_fresh_at sn x /\ ptr_covers G tn x s cap ==> ptr_covers Gf tf x z cap) /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    alloca_history func z /\ allocas_from lo z /\ lo <= z.vs_alloca_next /\
    s.vs_alloca_next <= z.vs_alloca_next /\ s0.vs_alloca_next <= z.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\ z.vs_alloca_next < dimword (:256) /\
    z.vs_labels = s.vs_labels /\ ~z.vs_halted /\
    z.vs_current_bb = sc.cs_current_bb /\ z.vs_inst_idx = LENGTH sc.cs_current_insts /\
    sn.cs_next_var < sc.cs_next_var /\ sn.cs_next_id < sc.cs_next_id /\
    local_ptrs_reserved ce sc /\ post_value_type ce e = lowered_value_type ce e /\
    ptr_val_ok cx (post_value_type ce e) v op Gf tf z /\ ptr_buf_ok ce e op Gf z /\
    expr_store_bound cx (post_value_type ce e) v op z /\
    eval_operand op z = SOME w /\ op = Var root /\ not_fresh_at sc root /\
    ptr_covers Gf tf root z (type_memory_size rt) /\ op_taint tf op = {} /\
    value_has_type rt v /\ val_wf rt v /\
    (!mem. mem_agree_outside tf.t_mem z.vs_memory mem ==>
      val_in_memory rt v (w2n w) mem) /\
    FLOOKUP z.vs_allocas sn.cs_next_id = SOME (w2n w,type_memory_size rt) /\
    lo <= w2n w /\ w2n w + type_memory_size rt <= z.vs_alloca_next /\
    w2n w + type_memory_size rt < dimword (:256) /\
    (!aid b len. aid < sn.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
      regions_disjoint (w2n w) (type_memory_size rt) b len)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  drule_all default_slot_reached_read >>
  disch_then (CONJUNCTS_THEN2 assume_tac (qx_choose_then `v` strip_assume_tac)) >>
  `~is_word_type tag` by simp[] >>
  drule_all_then assume_tac compile_storage_lowered_value_type >>
  `post_value_type ce e = lowered_value_type ce e` by simp[post_value_type_lowered] >>
  qpat_x_assum `lowered_value_type ce e = expr_type e` kall_tac >>
  drule_then strip_assume_tac (cj 1 compile_expr_grows) >>
  `sa.cs_next_id <= sn.cs_next_id /\ sa.cs_next_var <= sn.cs_next_var` by decide_tac >>
  `local_ptrs_reserved ce sn` by
    (irule local_ptrs_reserved_next_var >> qexists `sa` >> asm_rewrite_tac[]) >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sn x` by
    (drule_at (Pat `compile_expr _ _ _ _ = _`) (cj 1 compiler_compile_var) >>
     simp[vv_operand_def] >> metis_tac[not_fresh_at_mono]) >>
  drule_all (Q.INST [`sm` |-> `sn`, `entry` |-> `s0`] copy_slot_rhs_endpoint_mods) >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`root`,`w`,`mid`,`buf`,`u`,`z`,`Gf`,`tf`]
       (map_every assume_tac o CONJUNCTS))) >>
  suspend "linked"
QED

Resume default_unwrap_slot_prefix_mods[linked]:
  `type_memory_size rt < dimword (:256)` by decide_tac >>
  `type_memory_bytes ce (lowered_value_type ce e) <= type_memory_size rt` by
    (qpat_assum `post_value_type ce e = lowered_value_type ce e`
       (SUBST1_TAC o SYM) >> asm_rewrite_tac[LESS_EQ_REFL]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    expr_post_mods H ctx func ce cx e es sa sc s0 ee v op z /\
    ghost_inv_at_mods (DF H) lo d ce cx ee Gf tf z /\
    ghost_kept_at lo ce es sa Gi ti s0 Gf tf /\
    ptr_val_ok cx (post_value_type ce e) v op Gf tf z /\ ptr_buf_ok ce e op Gf z /\
    expr_store_bound cx (post_value_type ce e) v op z /\
    FLOOKUP z.vs_allocas sn.cs_next_id = SOME (w2n w,type_memory_size rt) /\
    lo <= w2n w /\ w2n w + type_memory_size rt <= z.vs_alloca_next /\
    not_fresh_at sc root /\ wb_frame ce ee ee sn s z /\
    ghost_kept_at lo ce ee sn G tn s Gf tf /\
    (!x cap. not_fresh_at sn x /\ ptr_covers G tn x s cap ==> ptr_covers Gf tf x z cap)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >>
     qpat_x_assum `op = Var root` SUBST_ALL_TAC >>
     match_mp_tac (Q.INST [`nb` |-> `type_memory_size rt`, `sm` |-> `sn`,
                           `sb` |-> `sc`, `vv` |-> `LocatedValue tag p`]
       copy_materialized_rhs_post_mods) >> asm_rewrite_tac[LESS_EQ_REFL]) >>
  suspend "finish"
QED

Resume default_unwrap_slot_prefix_mods[finish]:
  qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func ce cx ee z` by
    (qpat_assum `expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ z`
       (strip_assume_tac o REWRITE_RULE [expr_post_mods_def,expr_post_def]) >>
     first_assum ACCEPT_TAC) >>
  drule_then assume_tac stmt_state_rel_allocas_below_fmp >>
  `z.vs_alloca_next < dimword (:256)` by
    (drule stmt_state_rel_alloca_room >> disch_then (ACCEPT_TAC o MATCH_MP alloca_room_next_lt)) >>
  `local_ptrs_reserved ce sc` by
    (irule local_ptrs_reserved_next_var >> qexists `sn` >> simp[]) >>
  `op_taint tf op = {}` by
    (qpat_assum `op = Var root` SUBST1_TAC >>
     qpat_assum `ptr_covers Gf tf root z _`
       (mp_tac o REWRITE_RULE [ptr_covers_def]) >> simp[NoAsms]) >>
  `z.vs_labels = s.vs_labels` by
    (qpat_assum `!D. gas_origin_ptr_path _ _ [] _`
       (qspec_then `DF (storage_trace_horizon ee.storage_trace)` mp_tac) >>
     disch_then (strip_assume_tac o MATCH_MP gas_origin_ptr_path_projections) >>
     drule gas_path_ptr_erase >>
     disch_then (mp_tac o MATCH_MP gas_path_code_labels) >> simp[]) >>
  `lo <= z.vs_alloca_next /\ s0.vs_alloca_next <= z.vs_alloca_next` by
    (qpat_assum `lo <= w2n w` mp_tac >>
     qpat_assum `w2n w + type_memory_size rt <= z.vs_alloca_next` mp_tac >>
     qpat_assum `s0.vs_alloca_next <= s.vs_alloca_next` mp_tac >>
     qpat_assum `s.vs_alloca_next <= z.vs_alloca_next` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  qpat_x_assum `op = Var root` SUBST_ALL_TAC >>
  qpat_x_assum `root = STRING _ _` kall_tac >>
  qexistsl [`v`,`z`,`Gf`,`tf`,`w`,`root`] >> asm_rewrite_tac[] >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >> asm_rewrite_tac[]
QED

Finalise default_unwrap_slot_prefix_mods
