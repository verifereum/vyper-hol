(* The unwrap's own copy starts after the caller's destination ALLOCA. *)
Theory bodyExtDefaultUnwrapCodeMods
Ancestors
  bodyFullPostsMods bodyAttributeReadOperandMods bodyLocalCopyPhysicalRhsMods
  bodyCopyCtorRhsRunMods bodyCopyRuntimeRhsRunMods bodyCopyMaterializedRhsPostMods
  bodyFullShadowBodyInv bodyFullHashKeccakFixed valueTypingMemoryProps exprLoweringProps
  bodyPtrDefs loweringPosts freshWrites stateRelProj exprSimCopy ptrDiscipline
  fragGasOriginPtr fragGasPathPtr fragGasPathFrameMem exprSimProps
  vyperStorageFootprint compileEnv words finite_map arithmetic context

Theorem default_code_read_layout[local]:
  immutable_holds (ce with ce_module := owner) cx ty raw addr ee s /\
  evaluate_type (get_tenv cx) ty = SOME rt /\
  read_result cx raw ee = (INL v,ee) ==>
  value_has_type rt v /\ w2n addr + type_memory_size rt < dimword (:256)
Proof
  strip_tac >> gvs[immutable_holds_def,sub_layout_def] >>
  `off + k < dimword (:256)` by decide_tac >>
  simp[w2n_n2w,LESS_MOD] >> decide_tac
QED

Theorem default_unwrap_code_prefix_mods:
  p.ptr_location = LocCode /\
  unwrap_value ce (LocatedValue ty p) sm = (op,sc) /\
  ptr_vv_ok cx (post_value_type ce e) raw (LocatedValue ty p) ee G tn s /\
  (ce.ce_is_ctor ==>
    ?v. read_result cx raw ee = (INL v,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
             eval_operand p.ptr_operand s = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
          val_in_memory rt v (w2n w) mem)) /\
  ~is_word_type (post_value_type ce e) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
  type_memory_bytes ce (post_value_type ce e) = type_memory_size rt /\
  type_memory_bytes ce (lowered_value_type ce e) <= type_memory_size rt /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func ce cx e es sa sm s0 ee raw (LocatedValue ty p) s /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  ghost_kept_at lo ce es sa Gi ti s0 G tn /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  local_ptrs_reserved ce sa /\ sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  fn_has_code sm sc func /\ fn_inst_ids_distinct func /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?v z Gf tf root w.
    read_result cx raw ee = (INL v,ee) /\ value_has_type rt v /\ val_wf rt v /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gf,tf)) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      expr_post_mods H ctx func ce cx e es sa sc s0 ee v op z /\
      ghost_inv_at_mods (DF H) lo d ce cx ee Gf tf z) /\
    ghost_kept_at lo ce es sa Gi ti s0 Gf tf /\
    wb_frame ce ee ee sm s z /\ ghost_kept_at lo ce ee sm G tn s Gf tf /\
    (!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
    (!x cap. not_fresh_at sm x /\ ptr_covers G tn x s cap ==> ptr_covers Gf tf x z cap) /\
    (!aid chunk. FLOOKUP s.vs_allocas aid = SOME chunk ==> FLOOKUP z.vs_allocas aid = SOME chunk) /\
    (!aid b len. aid < sm.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
      regions_disjoint (w2n w) (type_memory_size rt) b len) /\
    alloca_history func z /\ allocas_from lo z /\ lo <= z.vs_alloca_next /\
    s.vs_alloca_next <= z.vs_alloca_next /\ z.vs_alloca_next < dimword (:256) /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
    z.vs_labels = s.vs_labels /\ ~z.vs_halted /\ z.vs_current_bb = sc.cs_current_bb /\
    z.vs_inst_idx = LENGTH sc.cs_current_insts /\ local_ptrs_reserved ce sc /\
    op = Var root /\ not_fresh_at sc root /\ eval_operand op z = SOME w /\
    ptr_val_ok cx (post_value_type ce e) v op Gf tf z /\ ptr_buf_ok ce e op Gf z /\
    expr_store_bound cx (post_value_type ce e) v op z /\
    ptr_covers Gf tf root z (type_memory_size rt) /\
    FLOOKUP z.vs_allocas sm.cs_next_id = SOME (w2n w,type_memory_size rt) /\
    sm.cs_next_id < sc.cs_next_id /\
    w2n w + type_memory_size rt <= z.vs_alloca_next /\
    (!mem. mem_agree_outside tf.t_mem z.vs_memory mem ==>
      val_in_memory rt v (w2n w) mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 H0 ee.storage_trace` by fs[Abbr `H0`,storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  `?v. read_result cx raw ee = (INL v,ee)` by
    (qpat_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
     drule_then (qx_choosel_then [`value`,`addr`] strip_assume_tac) attribute_read_operand_mods >>
     qexists `value` >> first_assum ACCEPT_TAC) >>
  drule_all local_copy_raw_code_source_mods >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac
      (qx_choosel_then [`owner`,`tops`,`addr`] (map_every assume_tac o CONJUNCTS))))) >>
  `evaluate_type (get_tenv cx) ty = SOME rt` by simp[] >>
  drule_all_then strip_assume_tac default_code_read_layout >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  `type_memory_size rt < dimword (:256)` by decide_tac >>
  `~is_word_type ty /\ type_memory_bytes ce ty = type_memory_size rt` by simp[] >>
  `val_wf rt v` by simp[value_has_type_memory_wf] >>
  `local_ptrs_reserved ce sm` by
    (irule local_ptrs_reserved_next_var >> qexists `sa` >> simp[]) >>
  `stmt_state_rel H0 ctx func ce cx ee s` by fs[vv_post_mods_def] >>
  drule_then assume_tac stmt_state_rel_allocas_below_fmp >>
  Cases_on `ce.ce_is_ctor` >- suspend "ctor" >> suspend "runtime"
QED

val finish_code_prefix =
  qpat_x_assum `op = Var root` SUBST_ALL_TAC >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    expr_post_mods H ctx func ce cx e es sa sc s0 ee v (Var root) z /\
    ghost_inv_at_mods (DF H) lo d ce cx ee Gf tf z /\
    ghost_kept_at lo ce es sa Gi ti s0 Gf tf /\
    ptr_val_ok cx (post_value_type ce e) v (Var root) Gf tf z /\
    ptr_buf_ok ce e (Var root) Gf z /\
    expr_store_bound cx (post_value_type ce e) v (Var root) z /\
    FLOOKUP z.vs_allocas sm.cs_next_id = SOME (w2n w,type_memory_size rt) /\
    lo <= w2n w /\ w2n w + type_memory_size rt <= z.vs_alloca_next /\ not_fresh_at sc root /\
    wb_frame ce ee ee sm s z /\ ghost_kept_at lo ce ee sm G tn s Gf tf /\
    (!x cap. not_fresh_at sm x /\ ptr_covers G tn x s cap ==> ptr_covers Gf tf x z cap)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` (drule_then strip_assume_tac)) >>
     mp_tac (Q.INST [`nb` |-> `type_memory_size rt`, `sb` |-> `sc`,
                     `tv` |-> `raw`, `vv` |-> `LocatedValue ty p`, `D` |-> `DF H`]
       (INST_TYPE [alpha |-> ``:256``] copy_materialized_rhs_post_mods)) >>
     (impl_tac >- asm_rewrite_tac[LESS_EQ_REFL]) >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `H0` (drule_then strip_assume_tac)) >>
  `stmt_state_rel H0 ctx func ce cx ee z` by fs[expr_post_mods_def,expr_post_def] >>
  `z.vs_alloca_next < dimword (:256)` by
    (drule stmt_state_rel_alloca_room >> disch_then (ACCEPT_TAC o MATCH_MP alloca_room_next_lt)) >>
  `local_ptrs_reserved ce sc` by
    (irule local_ptrs_reserved_next_var >> qexists `sm` >> simp[]) >>
  `lo <= z.vs_alloca_next` by decide_tac >>
  qpat_x_assum `root = STRING _ _` kall_tac >>
  qexistsl [`v`,`z`,`Gf`,`tf`,`root`,`w`] >> asm_rewrite_tac[] >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >> asm_rewrite_tac[];

Resume default_unwrap_code_prefix_mods[ctor]:
  qpat_assum `ce.ce_is_ctor ==> w2n _ + _ <= lo /\ _` (drule_then strip_assume_tac) >>
  drule_all (Q.INST [`sb` |-> `sm`] copy_ctor_rhs_endpoint_mods) >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`z`,`Gf`,`tf`,`root`,`w`,`u`] (map_every assume_tac o CONJUNCTS))) >>
  `!j. j < w2n w \/ w2n w+type_memory_size rt <= j ==> j IN tf.t_mem ==> j IN tn.t_mem` by
    (rpt gen_tac >> disch_tac >> first_x_assum (drule_then (fn th => simp[th]))) >>
  finish_code_prefix
QED

Resume default_unwrap_code_prefix_mods[runtime]:
  qpat_assum `~ce.ce_is_ctor ==> _ /\ _` (drule_then strip_assume_tac) >>
  drule_all copy_runtime_rhs_endpoint_mods >>
  disch_then (qspecl_then [`explicit`,`PG`,`G`]
    (qx_choosel_then [`z`,`Gf`,`tf`,`root`,`w`,`u`] (map_every assume_tac o CONJUNCTS))) >>
  `!j. j < w2n w \/ w2n w+type_memory_size rt <= j ==> j IN tf.t_mem ==> j IN tn.t_mem` by
    simp[pred_setTheory.IN_DIFF] >>
  `z.vs_labels = s.vs_labels` by
    (qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) [] _` (qspec_then `DF H0` mp_tac) >>
     disch_then (strip_assume_tac o MATCH_MP gas_origin_ptr_path_projections) >>
     drule gas_path_ptr_erase >>
     disch_then (mp_tac o MATCH_MP gas_path_code_labels) >> simp[]) >>
  finish_code_prefix
QED

Finalise default_unwrap_code_prefix_mods
