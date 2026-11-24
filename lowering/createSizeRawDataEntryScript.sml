Theory createSizeRawDataEntry
Ancestors
  gasShadowCompileBase
  e2eDefs exprSimFullBundleProps fragExec fragGasOrigin gasExplicitSites gasSummary
  s1PrefixDefs venomExecSemantics venomState vyperCreate vyperState relation list words
  createMarkedPath pair bodyFullIfExpReach arithmetic exprLowering stmtLoweringMono
  vfmConstants compileEnv exprLoweringProps exprBodyPreProps exprSimSource bodyMemoryDefs
  freshWrites rich_list exprSimHypsDefs vyperTypeSystem exprSimWordArgs bodyPtrDefs
  loweringPosts context createSizeRawSource fragGasPath vyperAST vyperStorageFootprint
  vyperTyping integer_word loweringStateRelDefs contextRawReachable ptrDiscipline
  createBlueprintRawCopyLayout createSizeRawSnapshotEntry bodySim loweringShapeDefs
  createExprSizeExitDefs createSizePrefixReplay createSizeBlueprintKeywordReplay
  createSizeRawHeaderReplay createSizeRawReplay

(* Forget the mark accumulator, keeping the same target execution. *)
Theorem raw_prefix_origin_rtc[local]:
  create_expr_prefix a b explicit ctx fn u marks v ==>
    RTC (\p q. ?ms. gas_origin_edge F explicit ctx fn p ms (OK q)) u v
Proof
  strip_tac >> drule_then irule create_expr_prefix_rtc_project >>
  simp[create_prefix_step_def] >> metis_tac[]
QED

Theorem create_raw_data_entry_from_replay:
  body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shadow_ctx /\
  expr_body_pre ce cx env (Call ann (CreateTarget RawCreate hs rof ks) (e::v::rest) df) es /\
  raw_bytecode_replay_at (DF,lo,dep,ctx,shadow_ctx,PG,func,shadow_func)
    tops ce cx env e es (st0,sa,a,shadow_sa,shadow_a,vv,s0,G0,tn0) /\
  expr_vv_sim_full_pre (DF,lo,dep,ctx,shadow_ctx,PG : (num # num) option list,func,shadow_func)
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
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
  ?p tv code Gr tnr lenvar datavar.
    eval_expr cx e (es with gas_obs := gas_explicit (ms ++ later) s0.vs_gas_readings ++ tail) = (INL tv,p) /\
    p.gas_obs = gas_explicit later r.vs_gas_readings ++ tail /\
    read_result cx tv p = (INL (BytesV code),p) /\
    read_result cx tv (p with gas_obs := []) = (INL (BytesV code),p with gas_obs := []) /\
    bind (eval_exprs cx ((if hs then FRONT rest else rest) ++
                       v :: (if hs then [LAST rest] else [])))
      (\vs. eval_create_operands cx RawCreate hs rof (MAP expr_type (e::v::rest))
        (blueprint_literal_offset cx hs (e::v::rest)) (BytesV code::vs)) p = (res,ee) /\
    valid_horizon cx st0 H p.storage_trace /\ expr_sim_inv ce cx env p /\
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
       storage_well_formed_on cx p (FST h) /\
       ghost_inv_at (DF h) lo dep ce cx p Gr tnr r) /\
    FLOOKUP r.vs_allocas a.cs_next_id =
      SOME (buffer_allocation_base u a.cs_next_id,type_memory_bytes ce (lowered_value_type ce e)) /\
    lookup_var lenvar r = SOME (n2w (LENGTH code)) /\
    lookup_var datavar r = SOME (n2w (buffer_allocation_base u a.cs_next_id + 32)) /\
    not_fresh_at d lenvar /\ not_fresh_at d datavar /\
    op_taint tnr (Var lenvar) = {} /\ ptr_covers Gr tnr datavar r (LENGTH code) /\
    w2n (n2w (buffer_allocation_base u a.cs_next_id + 32) : bytes32) + LENGTH code <= r.vs_alloca_next
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (SPEC_ALL create_raw_bytecode_header_from_replay) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac
  >- (disj1_tac >> goal_assum (drule_at Any) >> simp[]) >>
  qpat_assum `expr_vv_sim_full_pre _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [expr_vv_sim_full_pre_def]) >>
  qpat_assum `!h. valid_horizon _ _ h p.storage_trace ==> _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  `ci_mono sa a` by metis_tac[ci_mono_compile_expr_sa, SND] >>
  `sa.cs_next_var <= a.cs_next_var` by fs[ci_mono_def] >>
  `!h. valid_horizon cx st0 h p.storage_trace ==>
      stmt_state_rel h ctx func ce cx (p with gas_obs := []) u /\
      storage_well_formed_on cx (p with gas_obs := []) (FST h) /\
      ghost_inv_at (DF h) lo dep ce cx (p with gas_obs := []) G tn u` by
    (gen_tac >> disch_tac >>
     qpat_assum `!h. valid_horizon _ _ h p.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
       (drule_then (strip_assume_tac o REWRITE_RULE [vv_post_def])) >> simp[]) >>
  `return_buf_frame dep ce a u` by
    (irule return_buf_frame_frame >>
     qpat_assum `return_buf_frame dep ce sa s0` (irule_at Any) >>
     fs[vv_post_def]) >>
  `~u.vs_halted` by
    (drule bodyFullIfExpReachTheory.gas_origin_ptr_path_erase >>
     disch_then (mp_tac o MATCH_MP gas_path_normal) >> simp[]) >>
  `(!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at a x) /\
   (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at a x)` by
     metis_tac[not_fresh_at_mono] >>
  `RTC (\x t. ?ms. gas_origin_edge F (gas_explicit_sites ctx shadow_ctx) ctx func x ms (OK t)) u r` by
    (imp_res_tac raw_prefix_origin_rtc >> metis_tac[RTC_TRANS]) >>
  mp_tac (Q.INST [`k` |-> `n`, `ac` |-> `d`, `len_op` |-> `len`, `data_op` |-> `data`,
                  `explicit` |-> `gas_explicit_sites ctx shadow_ctx`,
                  `obs` |-> `gas_explicit (ms ++ later) s0.vs_gas_readings ++ tail`]
           (Q.INST [`d` |-> `dep`] create_raw_snapshot_payload_entry)) >>
  (impl_tac >-
    (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
     gen_tac >> disch_tac >>
     qpat_assum `!tr. vv_location vv = SOME (slot_loc tr) ==> _`
       (drule_then strip_assume_tac) >>
     qexistsl [`buf`,`sm`,`x`,`exit`] >> asm_rewrite_tac[])) >> strip_tac >>
  suspend "entry"
QED
Resume create_raw_data_entry_from_replay[entry]:
  `ci_mono a d` by
    metis_tac[ci_mono_trans, ci_mono_compile_create_snapshot, ci_mono_emit_op, SND] >>
  `a.cs_next_var <= d.cs_next_var` by fs[ci_mono_def] >>
  `local_ptrs_reserved ce d` by metis_tac[local_ptrs_reserved_next_var] >>
  `(!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at d x) /\
   (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at d x)` by
    metis_tac[not_fresh_at_mono] >>
  `?nm. gas_path ctx func s0 nm (OK r)` by
    (`gas_path ctx func s0 (LENGTH ms) (OK u)` by
       metis_tac[bodyFullIfExpReachTheory.gas_origin_ptr_path_erase] >>
     `gas_path ctx func u (LENGTH msS) (OK z)` by metis_tac[create_prefix_gas_path] >>
     `~z.vs_halted` by metis_tac[gas_path_normal] >>
     `gas_path ctx func z (LENGTH msL) (OK l)` by metis_tac[create_prefix_gas_path] >>
     `~l.vs_halted` by metis_tac[gas_path_normal] >>
     `gas_path ctx func l (LENGTH msD) (OK r)` by metis_tac[create_prefix_gas_path] >>
     qexists_tac `LENGTH ms + (LENGTH msS + (LENGTH msL + LENGTH msD))` >>
     irule gas_path_then >> qexists_tac `u` >> conj_tac >- first_assum ACCEPT_TAC >>
     irule gas_path_then >> qexists_tac `z` >> conj_tac >- first_assum ACCEPT_TAC >>
     irule gas_path_then >> qexists_tac `l` >> simp[]) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[body_inv_no_phi] >>
  `!i. active_inst func i r ==> frag_reachable ctx func s0 func i r` by
    (drule gas_path_reach >> disch_then (qspecl_then [`func`,`s0`,`r`] mp_tac) >>
     simp[contextRawReachableTheory.frag_reachable_start]) >>
  `!fn i s. frag_reachable ctx func r fn i s ==> dalloca_fmp_headroom i s` by
    metis_tac[contextRawReachableTheory.frag_reachable_trans] >>
  suspend "source"
QED
Resume create_raw_data_entry_from_replay[source]:
  `w2n (n2w (LENGTH code) : bytes32) <= bytelike_type_bound (lowered_value_type ce e)` by
    (`expr_body_pre ce cx env e
         (es with gas_obs := gas_explicit (ms ++ later) s0.vs_gas_readings ++ tail)` by
       simp[expr_body_pre_gas_obs] >>
     `bind (eval_expr cx e) (read_result cx)
         (es with gas_obs := gas_explicit (ms ++ later) s0.vs_gas_readings ++ tail) = (INL (BytesV code),p)` by
       simp[bind_def] >>
     drule_all create_blueprint_raw_copy_layout >> strip_tac >>
     `LENGTH code <= bytelike_type_bound (lowered_value_type ce e)` by
       fs[value_has_type_def, bytelike_type_bound_def, bound_length_def] >>
     `w2n (n2w (LENGTH code) : bytes32) <= LENGTH code` by
       simp[w2n_n2w, MOD_LESS_EQ, ZERO_LT_dimword] >> decide_tac) >>
  `hs ==> rest <> []` by
    (qpat_assum `expr_body_pre ce cx env (Call _ _ _ _) es`
       (strip_assume_tac o MATCH_MP (GEN_ALL exprBodyPrePropsTheory.expr_body_pre_static_facts)) >>
     drule create_raw_first_type >> simp[]) >>
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
  qexistsl [`p`,`tv`,`code`,`Gr`,`tnr`,`lenvar`,`datavar`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  gen_tac >> disch_tac >>
  qpat_assum `!h. valid_horizon _ _ h p.storage_trace ==> stmt_state_rel _ _ _ _ _ _ r /\ _`
    (drule_then strip_assume_tac) >>
  conj_tac >- fs[stmt_state_rel_gas_obs] >> conj_tac
  >- (irule (iffLR storage_well_formed_on_backends) >>
      qexists_tac `p with gas_obs := []` >> simp[]) >>
  qpat_assum `ghost_inv_at (DF h) _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [ghost_inv_at_def]) >>
  simp[ghost_inv_at_def] >> strip_tac >> first_assum ACCEPT_TAC
QED
Finalise create_raw_data_entry_from_replay

Theorem create_raw_data_entry_at_cuts:
  body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shadow_ctx /\
  expr_body_pre ce cx env (Call ann (CreateTarget RawCreate hs rof ks) (e::v::rest) df) es /\
  EVERY (create_operand_completed_ok cx) (create_operand_order RawCreate hs (e::v::rest)) /\
  expr_vv_sim_full_pre (DF,lo,dep,ctx,shadow_ctx,PG : (num # num) option list,func,shadow_func)
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
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
  ?p tv code Gr tnr lenvar datavar.
    eval_expr cx e (es with gas_obs := gas_explicit (ms ++ later) s0.vs_gas_readings ++ tail) = (INL tv,p) /\
    p.gas_obs = gas_explicit later r.vs_gas_readings ++ tail /\
    read_result cx tv p = (INL (BytesV code),p) /\
    read_result cx tv (p with gas_obs := []) = (INL (BytesV code),p with gas_obs := []) /\
    bind (eval_exprs cx ((if hs then FRONT rest else rest) ++
                       v :: (if hs then [LAST rest] else [])))
      (\vs. eval_create_operands cx RawCreate hs rof (MAP expr_type (e::v::rest))
        (blueprint_literal_offset cx hs (e::v::rest)) (BytesV code::vs)) p = (res,ee) /\
    valid_horizon cx st0 H p.storage_trace /\ expr_sim_inv ce cx env p /\
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
       storage_well_formed_on cx p (FST h) /\
       ghost_inv_at (DF h) lo dep ce cx p Gr tnr r) /\
    FLOOKUP r.vs_allocas a.cs_next_id =
      SOME (buffer_allocation_base u a.cs_next_id,type_memory_bytes ce (lowered_value_type ce e)) /\
    lookup_var lenvar r = SOME (n2w (LENGTH code)) /\
    lookup_var datavar r = SOME (n2w (buffer_allocation_base u a.cs_next_id + 32)) /\
    not_fresh_at d lenvar /\ not_fresh_at d datavar /\
    op_taint tnr (Var lenvar) = {} /\ ptr_covers Gr tnr datavar r (LENGTH code) /\
    w2n (n2w (buffer_allocation_base u a.cs_next_id + 32) : bytes32) + LENGTH code <= r.vs_alloca_next
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all raw_bytecode_replay_at_of_completed >> disch_tac >>
  mp_tac (SPEC_ALL create_raw_data_entry_from_replay) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >>
  disch_then ACCEPT_TAC
QED
