Theory createSizeRawDataEntryMods
Ancestors
  createSizeRawDataEntry createExprSizeExitDefsMods
  gasShadowCompileBase
  e2eDefs exprSimFullBundleProps fragExec fragGasOrigin gasExplicitSites gasSummary
  s1PrefixDefs venomExecSemantics venomState vyperCreate vyperState relation list words
  createMarkedPath pair bodyFullIfExpReach arithmetic exprLowering stmtLoweringMono
  vfmConstants compileEnv exprLoweringProps exprBodyPreProps exprSimSource bodyMemoryDefs
  freshWrites rich_list exprSimHypsDefs vyperTypeSystem exprSimWordArgs bodyPtrDefs
  loweringPosts context createSizeRawSourceMods fragGasPath vyperAST vyperStorageFootprint
  vyperTyping integer_word loweringStateRelDefs contextRawReachable ptrDiscipline
  createBlueprintRawCopyLayoutMods createSizeRawSnapshotEntryMods bodySim loweringShapeDefs
  createExprSizeExitDefs createSizePrefixReplayMods createSizeBlueprintKeywordReplayMods
  createSizeRawHeaderReplayMods createSizePrefixReplay bodyFullPostsMods

(* Replay the bytecode header, then carry its observations to the data cut. *)

Theorem create_raw_data_entry_at_cuts_mods:
  contract_inv mods exps ctx ce cx /\
  module_body_inv mods src tops ce cx /\ shadow_body_inv_mods mods exps ctx shadow_ctx /\
  expr_body_pre_mods mods ce cx env (Call ann (CreateTarget RawCreate hs rof ks) (e::v::rest) df) es /\
  EVERY (create_operand_completed_ok_mods mods exps cx) (create_operand_order RawCreate hs (e::v::rest)) /\
  expr_vv_sim_full_pre_mods (DF,lo,dep,ctx,shadow_ctx,PG : (num # num) option list,func,shadow_func)
    ce cx ty (Call ann (CreateTarget RawCreate hs rof ks) (e::v::rest) df) es
    (st0,sa,sb,shadow_sa,shadow_sb,parent_vv,s0,G0,tn0) /\
  compile_expr ce (expr_type e) e sa = (vv,a) /\
  compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) shadow_sa = (vv,shadow_a) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,a,shadow_sa,shadow_a) /\
  compile_create_snapshot ce vv (lowered_value_type ce e) a = (snap,b) /\
  emit_op MLOAD [snap] b = (len,c) /\ emit_op ADD [snap; Lit 32w] c = (data,d) /\
  fn_has_code a d func /\
  u.vs_current_bb = a.cs_current_bb /\ u.vs_inst_idx = LENGTH a.cs_current_insts /\
  z.vs_current_bb = b.cs_current_bb /\ z.vs_inst_idx = LENGTH b.cs_current_insts /\
  l.vs_current_bb = c.cs_current_bb /\ l.vs_inst_idx = LENGTH c.cs_current_insts /\
  r.vs_current_bb = d.cs_current_bb /\ r.vs_inst_idx = LENGTH d.cs_current_insts /\
  create_expr_prefix sa a (gas_explicit_sites ctx shadow_ctx) ctx func s0 ms u /\
  create_expr_prefix a b (gas_explicit_sites ctx shadow_ctx) ctx func u msS z /\
  create_expr_prefix b c (gas_explicit_sites ctx shadow_ctx) ctx func z msL l /\
  create_expr_prefix c d (gas_explicit_sites ctx shadow_ctx) ctx func l msD r /\
  eval_expr cx (Call ann (CreateTarget RawCreate hs rof ks) (e::v::rest) df)
    (es with gas_obs := gas_explicit (ms ++ (msS ++ msL ++ msD ++ later)) s0.vs_gas_readings ++ tail) = (res,ee) /\
  valid_horizon cx st0 H ee.storage_trace ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt_mods mods err) \/
  ?p tv code Gr tnr lenvar datavar.
    eval_expr cx e (es with gas_obs := gas_explicit (ms ++ later) s0.vs_gas_readings ++ tail) = (INL tv,p) /\
    p.gas_obs = gas_explicit later r.vs_gas_readings ++ tail /\
    read_result cx tv p = (INL (BytesV code),p) /\
    read_result cx tv (p with gas_obs := []) = (INL (BytesV code),p with gas_obs := []) /\
    bind (eval_exprs cx ((if hs then FRONT rest else rest) ++
                       v :: (if hs then [LAST rest] else [])))
      (\vs. eval_create_operands cx RawCreate hs rof (MAP expr_type (e::v::rest))
        (blueprint_literal_offset cx hs (e::v::rest)) (BytesV code::vs)) p = (res,ee) /\
    valid_horizon cx st0 H p.storage_trace /\ expr_sim_inv_mods mods ce cx env p /\
    eval_operand len l = SOME (n2w (LENGTH code)) /\
    w2n (n2w (LENGTH code) : bytes32) <= bytelike_type_bound (lowered_value_type ce e) /\
    msS = [] /\ msL = [] /\ msD = [] /\
    len = Var lenvar /\ data = Var datavar /\
    return_buf_frame dep ce d r /\ alloca_history func r /\ ~r.vs_halted /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp r) /\
    r.vs_current_bb = d.cs_current_bb /\ r.vs_inst_idx = LENGTH d.cs_current_insts /\
    local_ptrs_reserved ce d /\
    (!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at d x) /\
    (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at d x) /\
    (!fn i s. frag_reachable ctx func r fn i s ==> dalloca_fmp_headroom i s) /\
    (!h. valid_horizon cx st0 h p.storage_trace ==>
       stmt_state_rel h ctx func ce cx p r /\
       immutable_frame_mods func ce cx p r /\
       storage_well_formed_on cx p (FST h) /\
       ghost_inv_at_mods (DF h) lo dep ce cx p Gr tnr r) /\
    FLOOKUP r.vs_allocas a.cs_next_id =
      SOME (buffer_allocation_base u a.cs_next_id,type_memory_bytes ce (lowered_value_type ce e)) /\
    lookup_var lenvar r = SOME (n2w (LENGTH code)) /\
    lookup_var datavar r = SOME (n2w (buffer_allocation_base u a.cs_next_id + 32)) /\
    not_fresh_at d lenvar /\ not_fresh_at d datavar /\
    op_taint tnr (Var lenvar) = {} /\ ptr_covers Gr tnr datavar r (LENGTH code) /\
    w2n (n2w (buffer_allocation_base u a.cs_next_id + 32) : bytes32) + LENGTH code <= r.vs_alloca_next
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all create_raw_bytecode_header_at_cuts_mods >> strip_tac
  >- (disj1_tac >> qexists_tac `err` >> simp[]) >>
  qpat_assum `expr_vv_sim_full_pre_mods _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_vv_sim_full_pre_mods_def]) >>
  qpat_assum `!h. valid_horizon _ _ h p.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  `sa.cs_next_var <= a.cs_next_var` by
    metis_tac[ci_mono_compile_expr_sa, ci_mono_def, SND] >>
  `!h. valid_horizon cx st0 h p.storage_trace ==>
      stmt_state_rel h ctx func ce cx (p with gas_obs := []) u /\
      storage_well_formed_on cx (p with gas_obs := []) (FST h) /\
      ghost_inv_at_mods (DF h) lo dep ce cx (p with gas_obs := []) G tn u` by
    (gen_tac >> disch_tac >>
     qpat_assum `!h. valid_horizon _ _ h p.storage_trace ==> _`
       (drule_then (strip_assume_tac o REWRITE_RULE [vv_post_mods_def])) >> simp[]) >>
  `return_buf_frame dep ce a u` by
    (irule return_buf_frame_frame >>
     qpat_assum `return_buf_frame dep ce sa s0` (irule_at Any) >>
     fs[vv_post_mods_def]) >>
  `gas_path ctx func s0 (LENGTH ms) (OK u)` by
    metis_tac[bodyFullIfExpReachTheory.gas_origin_ptr_path_erase] >>
  `~u.vs_halted` by metis_tac[gas_path_normal] >>
  `(!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at a x) /\
   (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at a x)` by
     metis_tac[not_fresh_at_mono] >>
  `RTC (\x t. ?ms. gas_origin_edge F (gas_explicit_sites ctx shadow_ctx) ctx func x ms (OK t)) u r` by
    suspend "rtc" >>
  suspend "snapshot"
QED

Resume create_raw_data_entry_at_cuts_mods[rtc]:
  `!x a b ms t. create_expr_prefix a b (gas_explicit_sites ctx shadow_ctx) ctx func x ms t ==>
    RTC (\p q. ?marks. gas_origin_edge F (gas_explicit_sites ctx shadow_ctx) ctx func p marks (OK q)) x t` by
    (rpt gen_tac >> strip_tac >> drule_then irule create_expr_prefix_rtc_project >>
     simp[create_prefix_step_def] >> metis_tac[]) >>
  metis_tac[RTC_TRANS]
QED

Resume create_raw_data_entry_at_cuts_mods[snapshot]:
  `fn_inst_ids_distinct func` by fs[expr_sim_full_code_def] >>
  `!tr. vv_location vv = SOME (slot_loc tr) ==>
    ?buf m y exit. compile_alloc_buffer (type_memory_bytes ce (lowered_value_type ce e)) a = (buf,m) /\
      fn_has_code m b func /\ lookup_block b.cs_current_bb func.fn_blocks = SOME exit /\
      phi_prefix_length exit.bb_instructions = 0 /\
      y.vs_current_bb = m.cs_current_bb /\ y.vs_inst_idx = LENGTH m.cs_current_insts /\
      z.vs_current_bb = b.cs_current_bb /\ z.vs_inst_idx = 0 /\
      run_inst_seq (emitted_insts a m) u = OK (y with vs_inst_idx := u.vs_inst_idx) /\
      RTC (\x t. (x.vs_current_bb <> b.cs_current_bb \/ x.vs_inst_idx <> 0) /\
                 ?ms. gas_origin_edge F (gas_explicit_sites ctx shadow_ctx) ctx func x ms (OK t)) y z` by
    (qpat_assum `z.vs_current_bb = _` (fn th => pure_once_rewrite_tac [th]) >>
     pure_rewrite_tac [REFL_CLAUSE, AND_CLAUSES] >> first_assum ACCEPT_TAC) >>
  drule_all create_raw_snapshot_payload_entry_mods >> strip_tac >>
  suspend "entry"
QED
Resume create_raw_data_entry_at_cuts_mods[entry]:
  `ci_mono a d` by
    metis_tac[ci_mono_trans, ci_mono_compile_create_snapshot, ci_mono_emit_op, SND] >>
  `a.cs_next_var <= d.cs_next_var` by fs[ci_mono_def] >>
  `local_ptrs_reserved ce d` by metis_tac[local_ptrs_reserved_next_var] >>
  `(!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at d x) /\
   (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at d x)` by
    metis_tac[not_fresh_at_mono] >>
  `?nm. gas_path ctx func s0 nm (OK r)` by
    (`gas_path ctx func u (LENGTH msS) (OK z)` by metis_tac[create_prefix_gas_path] >>
     `~z.vs_halted` by metis_tac[gas_path_normal] >>
     `gas_path ctx func z (LENGTH msL) (OK l)` by metis_tac[create_prefix_gas_path] >>
     `~l.vs_halted` by metis_tac[gas_path_normal] >>
     `gas_path ctx func l (LENGTH msD) (OK r)` by metis_tac[create_prefix_gas_path] >>
     qexists_tac `LENGTH ms + (LENGTH msS + (LENGTH msL + LENGTH msD))` >>
     irule gas_path_then >> qexists_tac `u` >> conj_tac >- first_assum ACCEPT_TAC >>
     irule gas_path_then >> qexists_tac `z` >> conj_tac >- first_assum ACCEPT_TAC >>
     irule gas_path_then >> qexists_tac `l` >> simp[]) >>
  `MEM func ctx.ctx_functions` by fs[expr_sim_full_code_def] >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> drule_all body_inv_no_phi_mods >> simp[]) >>
  `!i. active_inst func i r ==> frag_reachable ctx func s0 func i r` by
    (drule gas_path_reach >> disch_then (qspecl_then [`func`,`s0`,`r`] mp_tac) >>
     simp[contextRawReachableTheory.frag_reachable_start]) >>
  `!fn i s. frag_reachable ctx func r fn i s ==> dalloca_fmp_headroom i s` by
    metis_tac[contextRawReachableTheory.frag_reachable_trans] >>
  suspend "source"
QED

Resume create_raw_data_entry_at_cuts_mods[source]:
  `w2n (n2w (LENGTH code) : bytes32) <= bytelike_type_bound (lowered_value_type ce e)` by
    (`expr_body_pre_mods mods ce cx env e
        (es with gas_obs := gas_explicit (ms ++ later) s0.vs_gas_readings ++ tail)` by simp[] >>
     `bind (eval_expr cx e) (read_result cx)
        (es with gas_obs := gas_explicit (ms ++ later) s0.vs_gas_readings ++ tail) = (INL (BytesV code),p)` by
       simp[bind_def] >>
     drule_all create_blueprint_raw_copy_layout_mods >> strip_tac >>
     `LENGTH code <= bytelike_type_bound (lowered_value_type ce e)` by
       fs[value_has_type_def, bytelike_type_bound_def, bound_length_def] >>
     `w2n (n2w (LENGTH code) : bytes32) <= LENGTH code` by
       simp[w2n_n2w, MOD_LESS_EQ, ZERO_LT_dimword] >> decide_tac) >>
  `hs ==> rest <> []` by
    (qpat_assum `expr_body_pre_mods _ _ _ _ (Call _ _ _ _) _`
       (mp_tac o MATCH_MP expr_body_pre_mods_well_typed) >>
     disch_then (strip_assume_tac o MATCH_MP createSizeRawSourceTheory.create_raw_first_type) >>
     first_assum ACCEPT_TAC) >>
  `TAKE (LENGTH rest - (if hs then 1 else 0)) rest ++
      v :: DROP (LENGTH rest - (if hs then 1 else 0)) rest =
    (if hs then FRONT rest else rest) ++ v :: (if hs then [LAST rest] else [])` by
    (reverse (Cases_on `hs`) >- simp[] >>
     `rest <> []` by fs[] >>
     `0 < LENGTH rest` by (Cases_on `rest` >> fs[]) >>
     simp[FRONT_BY_TAKE, DROP_PREn_LAST_CONS]) >>
  pop_assum (fn eq => qpat_x_assum `bind (eval_exprs cx _) _ p = (res,ee)`
    (assume_tac o PURE_REWRITE_RULE [eq])) >>
  disj2_tac >>
  rename1 `lookup_var datavar r = SOME (n2w (buffer_allocation_base u a.cs_next_id + 32))` >>
  rename1 `lookup_var lenvar r = SOME (n2w (LENGTH code))` >>
  qexistsl_tac [`p`,`tv`,`code`,`Gr`,`tnr`,`lenvar`,`datavar`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  gen_tac >> disch_tac >>
  qpat_assum `!h. valid_horizon _ _ h p.storage_trace ==> stmt_state_rel _ _ _ _ _ _ r /\ _`
    (drule_then strip_assume_tac) >>
  conj_tac >- fs[stmt_state_rel_gas_obs] >>
  conj_tac
  >- (`immutable_frame_mods func ce cx (p with gas_obs := []) r <=>
       immutable_frame_mods func ce cx p r` by
        simp_tac (srw_ss())
          [immutable_frame_mods_def, bodyInvSplitTheory.immutables_rel_mods_def, immutables_rel_def,
           bodyInvSplitTheory.immutable_alloca_sep_mods_def, immutable_alloca_sep_def] >>
      metis_tac[]) >>
  conj_tac
  >- (irule (iffLR storage_well_formed_on_backends) >>
      qexists_tac `p with gas_obs := []` >> simp[]) >>
  `ghost_inv_at_mods (DF h) lo dep ce cx (p with gas_obs := []) Gr tnr r <=>
   ghost_inv_at_mods (DF h) lo dep ce cx p Gr tnr r` by
    simp_tac (srw_ss()) [bodyFullShadowBodyInvTheory.ghost_inv_at_mods_def] >>
  metis_tac[]
QED
Finalise create_raw_data_entry_at_cuts_mods
