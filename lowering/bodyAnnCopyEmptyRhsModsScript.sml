(* The empty nonword declaration executes the raw RHS at the allocation cut.
   It does not execute an unwrap or a value-sized copy. *)
Theory bodyAnnCopyEmptyRhsMods
Ancestors
  bodyFullPostsMods bodyMemoryDefs memoryLocalRhsProps exprBodyPreProps
  vyperTypeEvalCaseProofs vyperTypeEnvPreservation vyperEvalExprPreservesScopesDom
  vyperStorageTrace vyperStorageFootprint assignTuplePtrCopyLen
  exprLoweringProps stmtSimDefs bodyPtrDefs bodySimFull vyperState

Theorem empty_rhs_value_mods[local]:
  expr_body_pre_mods mods ce cx env e es /\
  is_empty_value_expr e /\ has_length_word typ /\
  type_widens_to env.type_defs (expr_type e) typ /\
  evaluate_type (get_tenv cx) typ = SOME tyv /\
  eval_expr cx e st = (INL tv,mid) ==>
  tv = Value (default_value tyv)
Proof
  strip_tac >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_then (mp_tac o MATCH_MP expr_sim_inv_mods_env) expr_body_pre_mods_inv >>
  strip_tac >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  irule memory_rhs_empty_eval_destination >>
  goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >>
  qexistsl_tac [`env`,`typ`] >> simp[]
QED

Theorem ann_copy_empty_rhs_mods:
  compile_expr ce ty e a = (vv,b) /\
  compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr e) shadow_a = (vv,shadow_b) /\
  gas_shadow_state a shadow_a /\ gas_shadow_state b shadow_b /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code a b func /\ fn_has_code shadow_a shadow_b shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce a /\
  (!H. dead_lo_ok_mods H (DF H) lo ce cx) /\
  (!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at a x) /\
  (!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at a x) /\
  gas_admissible (eval_expr cx e) expr_vv_res_ok es /\
  return_buf_frame d ce a entry /\ alloca_history func entry /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp entry) /\
  (!fn inst z. frag_reachable ctx func entry fn inst z ==> dalloca_fmp_headroom inst z) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func ce cx es entry /\
    immutable_frame_mods func ce cx es entry /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at_mods (DF H) lo d ce cx es Ga tna entry) /\
  ~entry.vs_halted /\ entry.vs_current_bb = a.cs_current_bb /\
  entry.vs_inst_idx = LENGTH a.cs_current_insts /\
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx ty e es /\
  expr_body_pre_mods mods ce cx env e es /\
  is_empty_value_expr e /\ has_length_word typ /\
  type_widens_to env.type_defs (expr_type e) typ /\
  evaluate_type (get_tenv cx) typ = SOME tyv /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_scopes id es.scopes = NONE /\ not_fresh_at a p /\
  lookup_var p entry = SOME w /\ ptr_covers Ga tna p entry sz /\
  FLOOKUP entry.vs_allocas aid = SOME (w2n w,sz) /\
  w2n w + sz < dimword (:256) /\ w2n w + sz <= entry.vs_alloca_next /\
  sa.cs_next_id <= a.cs_next_id /\
  (!x. not_fresh_at sa x ==> not_fresh_at a x) /\
  s0.vs_alloca_next <= entry.vs_alloca_next /\
  (!x z. not_fresh_at sa x /\ lookup_var x s0 = SOME z ==>
    lookup_var x entry = SOME z) /\
  (!ad ent. FLOOKUP s0.vs_allocas ad = SOME ent ==>
    FLOOKUP entry.vs_allocas ad = SOME ent) /\
  alloca_frame old es sa s0 ce es entry /\
  ghost_kept_at lo old es sa G0 tn0 s0 Ga tna /\
  (* The linked source-post rule, specialized to this run. *)
  (!Q Q' R.
     gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       ce.ce_modules cx st0 (eval_expr cx e) (es,entry,Ga,tna) Q R /\
     (!H res mid G tn u.
       (?xs. !tail. eval_expr cx e (es with gas_obs := xs ++ tail) =
                   (res,mid with gas_obs := tail)) /\
       mid.gas_obs = [] /\ ~u.vs_halted /\
       valid_horizon cx st0 H mid.storage_trace /\ Q H res mid G tn u ==>
       Q' H res mid G tn u) ==>
     gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       ce.ce_modules cx st0 (eval_expr cx e) (es,entry,Ga,tna) Q' R) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    ce.ce_modules cx st0 (eval_expr cx e) (es,entry,Ga,tna)
    (\H res mid G tn u.
      res = INL (Value (default_value tyv)) /\
      (!xs.
        (!tail. eval_expr cx e (es with gas_obs := xs ++ tail) =
                  (res,mid with gas_obs := tail)) ==>
        !tail. bind (eval_expr cx e) (read_result cx)
                  (es with gas_obs := xs ++ tail) =
                (INL (default_value tyv),mid with gas_obs := tail)) /\
      vv_post_mods H ctx func ce cx e es a b entry mid
        (Value (default_value tyv)) vv u /\
      ~u.vs_halted /\ u.vs_current_bb = b.cs_current_bb /\
      u.vs_inst_idx = LENGTH b.cs_current_insts /\ alloca_history func u /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
      entry.vs_alloca_next <= u.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d ce cx mid G tn u /\
      ghost_kept_at lo ce es a Ga tna entry G tn /\
      return_buf_frame d ce b u /\ MAP FDOM mid.scopes = MAP FDOM es.scopes /\
      lookup_scopes id mid.scopes = NONE /\ not_local_ptr ce mid.scopes p /\
      lookup_var p u = SOME w /\ ptr_covers G tn p u sz /\
      FLOOKUP u.vs_allocas aid = SOME (w2n w,sz) /\
      w2n w + sz < dimword (:256) /\ w2n w + sz <= u.vs_alloca_next /\
      (!x z. not_fresh_at sa x /\ lookup_var x s0 = SOME z ==>
        lookup_var x u = SOME z) /\
      (!ad ent. FLOOKUP s0.vs_allocas ad = SOME ent ==>
        FLOOKUP u.vs_allocas ad = SOME ent) /\
      (!x. not_fresh_at sa x ==> FLOOKUP G x = FLOOKUP G0 x /\
        op_taint tn (Var x) = op_taint tn0 (Var x)) /\
      s0.vs_alloca_next <= u.vs_alloca_next /\
      alloca_frame old es sa s0 ce mid u /\
      (!ad off len i.
        FLOOKUP s0.vs_allocas ad = SOME (off,len) /\ ad < sa.cs_next_id /\
        (!name x cap. local_region old es.scopes s0 name x cap ==>
          off + len <= x \/ x + cap <= off) /\
        off <= i /\ i < off + len /\ i IN tn.t_mem ==> i IN tn0.t_mem))
    (\H res mid gt rr. expr_exit res rr /\ halt_exit H cx mid res rr /\
      (ctx_has_dalloca ctx ==> !s. rr = Halt s ==> allocas_below_fmp s))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `expr_vv_sim_full_mods _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_full_mods_def]) >>
  disch_then (qspecl_then [`st0`,`a`,`b`,`shadow_a`,`shadow_b`,
    `vv`,`entry`,`Ga`,`tna`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_tac >>
  qpat_x_assum `!Q Q' R. _` (irule o SPEC_ALL) >>
  goal_assum (drule_at (Pat `gas_outcome_full_mods _ _ _ _ _ _ _ _`)) >>
  BETA_TAC >> rpt gen_tac >> strip_tac >> gvs[] >>
  suspend "endpoint"
QED

Resume ann_copy_empty_rhs_mods[endpoint]:
  qpat_x_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _` kall_tac >>
  `tv = Value (default_value tyv)` by
    (qpat_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` assume_tac) >>
     drule_all_then ACCEPT_TAC empty_rhs_value_mods) >>
  gvs[] >>
  conj_tac >- (rpt strip_tac >> simp[Once bind_def, read_result_def, return_def]) >>
  `MAP FDOM mid.scopes = MAP FDOM es.scopes` by
    (qpat_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` mp_tac) >>
     disch_then (mp_tac o MATCH_MP eval_expr_preserves_scopes_dom) >> simp[]) >>
  `valid_horizon cx st0 H es.storage_trace` by
    (qpat_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` mp_tac) >> strip_tac >>
     drule_at (Pat `f st = _`) valid_horizon_frame >>
     simp[evaluate_storage_trace_frame] >> disch_then drule >> simp[]) >>
  `stmt_state_rel H ctx func ce cx es entry` by
    (qpat_assum `!H. valid_horizon _ _ _ es.storage_trace ==> _`
      (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `lookup_scopes id mid.scopes = NONE` by
    (Cases_on `lookup_scopes id mid.scopes` >> simp[] >>
     drule_all lookup_scopes_same_fdoms_some >> simp[]) >>
  `not_local_ptr ce mid.scopes p` by
    (irule local_ptrs_reserved_not_live >> conj_tac
     >- (qexistsl_tac [`id`,`sz`] >> simp[]) >> qexists_tac `a` >> simp[]) >>
  `a.cs_next_var <= b.cs_next_var` by
    (qpat_assum `compile_expr _ _ _ a = _`
      (mp_then Any mp_tac (cj 1 compile_expr_grows)) >> simp[]) >>
  qhdtm_assum `vv_post_mods`
    (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
  `return_buf_frame d ce b u` by
    (irule return_buf_frame_frame >> qexistsl_tac [`ce`,`entry`,`a`] >> simp[]) >>
  `lookup_var p u = SOME w /\ FLOOKUP u.vs_allocas aid = SOME (w2n w,sz)` by
    (conj_tac >> first_assum irule >> simp[]) >>
  `ptr_covers G tn p u sz` by
    (irule ptr_covers_lookup_frame >> qexistsl_tac [`Ga`,`entry`,`tna`] >>
     fs[ghost_kept_at_def]) >>
  `alloca_frame ce es a entry ce mid u` by
    (qpat_assum `stmt_state_rel H ctx func ce cx es entry`
       (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) irule alloca_frame_of_mem_frame) >>
     asm_rewrite_tac[]) >>
  `alloca_frame old es sa s0 ce mid u` by
    (irule alloca_frame_trans >> qexistsl_tac [`ce`,`es`,`entry`,`a`] >> simp[]) >>
  suspend "older_resources"
QED

Resume ann_copy_empty_rhs_mods[older_resources]:
  fs[ghost_kept_at_def] >>
  qpat_assum `alloca_frame old es sa s0 ce es entry`
    (mp_then Any mp_tac alloca_taint_kept_trans) >>
  disch_then (qspecl_then [`tn`,`tna`,`tn0`,`a`] mp_tac) >>
  asm_rewrite_tac[] >> strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then [`ad`,`off`,`len`,`i`] mp_tac) >>
  simp[arithmeticTheory.ADD_COMM] >> disch_then irule >>
  qpat_assum `!name x cap. local_region old es.scopes s0 name x cap ==> _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[arithmeticTheory.ADD_COMM]
QED

Finalise ann_copy_empty_rhs_mods
