Theory createSizeRawHeaderReplay
Ancestors
  gasShadowCompileBase
  abiEncoderProps e2eDefs exprSimFullBundleProps fragExec fragGasOrigin gasExplicitSites
  gasSummary s1PrefixDefs venomExecSemantics venomInst venomState vyperCreate vyperState
  relation list words pair bodyFullIfExpReach arithmetic exprLowering vfmConstants
  compileEnv exprLoweringProps exprBodyPreProps exprSimCopy exprSimSource rich_list
  exprSimHypsDefs bodyPtrDefs loweringPosts context createSizeSnapshotLength vyperAST
  vyperStorageFootprint vyperValue integer_word valueEncoding loweringStateRelDefs
  exprSimMemDefs ptrDiscipline createSizeRawStraightBands createSizeRawSlotBand
  createSizeRawCodeSiteBound createSizeRawHeaderGeometry reasonEndpointResourcesPtr
  createBlueprintRawCopyLayout bodySim createExprSizeExitDefs createSizePrefixReplay
  createSizeRawReplay createSizeOperandPre

Theorem create_raw_header_bands[local]:
  compile_create_snapshot ce vv ty a = (snap,b) /\
  emit_op MLOAD [snap] b = (len,c) /\ emit_op ADD [snap; Lit 32w] c = (data,d) /\
  fn_has_code a d fn /\ fn_inst_ids_distinct fn /\
  vv_location vv <> SOME LocCalldata /\
  (!bb. MEM bb fn.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  u.vs_current_bb = a.cs_current_bb /\ u.vs_inst_idx = LENGTH a.cs_current_insts /\
  z.vs_current_bb = b.cs_current_bb /\ z.vs_inst_idx = LENGTH b.cs_current_insts /\
  l.vs_current_bb = c.cs_current_bb /\ l.vs_inst_idx = LENGTH c.cs_current_insts /\
  r.vs_current_bb = d.cs_current_bb /\ r.vs_inst_idx = LENGTH d.cs_current_insts /\
  create_expr_prefix a b explicit ctx fn u msS z /\
  create_expr_prefix b c explicit ctx fn z msL l /\
  create_expr_prefix c d explicit ctx fn l msD r ==>
  msS = [] /\ msL = [] /\ msD = [] /\
  r.vs_gas_readings = u.vs_gas_readings /\
  run_inst_seq (emitted_insts b c) z = OK (l with vs_inst_idx := z.vs_inst_idx) /\
  run_inst_seq (emitted_insts c d) l = OK (r with vs_inst_idx := l.vs_inst_idx) /\
  ((vv_location vv = NONE \/ vv_location vv = SOME LocMemory \/ vv_location vv = SOME LocCode) ==>
   run_inst_seq (emitted_insts a b) u = OK (z with vs_inst_idx := u.vs_inst_idx) /\
   run_inst_seq (emitted_insts a c) u = OK (l with vs_inst_idx := u.vs_inst_idx)) /\
  (!tr. vv_location vv = SOME (slot_loc tr) ==>
    ?buf sm x exit.
      compile_alloc_buffer (type_memory_bytes ce ty) a = (buf,sm) /\
      fn_has_code a sm fn /\ fn_has_code sm b fn /\
      lookup_block b.cs_current_bb fn.fn_blocks = SOME exit /\
      phi_prefix_length exit.bb_instructions = 0 /\
      x.vs_current_bb = sm.cs_current_bb /\ x.vs_inst_idx = LENGTH sm.cs_current_insts /\
      z.vs_inst_idx = 0 /\
      run_inst_seq (emitted_insts a sm) u = OK (x with vs_inst_idx := u.vs_inst_idx) /\
      RTC (\v w. (v.vs_current_bb <> b.cs_current_bb \/ v.vs_inst_idx <> 0) /\
                 ?ms. gas_origin_edge F explicit ctx fn v ms (OK w)) x z)
Proof
  pure_rewrite_tac[create_expr_prefix_marked] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `cs_extends a b /\ cs_extends b c /\ cs_extends c d` by
    metis_tac[ci_mono_def, ci_mono_compile_create_snapshot, ci_mono_emit_op, SND] >>
  `fn_has_code a c fn /\ fn_has_code a b fn /\ fn_has_code b c fn /\ fn_has_code c d fn` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `!p ms q. create_prefix_step a b explicit ctx fn p ms q ==>
     (p.vs_current_bb <> b.cs_current_bb \/ p.vs_inst_idx <> LENGTH b.cs_current_insts) /\
     gas_origin_edge F explicit ctx fn p ms (OK q)` by
    simp[create_prefix_step_def, PULL_EXISTS] >>
  `!p ms q. create_prefix_step b c explicit ctx fn p ms q ==>
     (p.vs_current_bb <> c.cs_current_bb \/ p.vs_inst_idx <> LENGTH c.cs_current_insts) /\
     gas_origin_edge F explicit ctx fn p ms (OK q)` by
    simp[create_prefix_step_def, PULL_EXISTS] >>
  `!p ms q. create_prefix_step c d explicit ctx fn p ms q ==>
     (p.vs_current_bb <> d.cs_current_bb \/ p.vs_inst_idx <> LENGTH d.cs_current_insts) /\
     gas_origin_edge F explicit ctx fn p ms (OK q)` by
    simp[create_prefix_step_def, PULL_EXISTS] >>
  drule_all (Q.INST [`ES` |-> `create_prefix_step a b explicit ctx fn`,
                     `length_edge` |-> `create_prefix_step b c explicit ctx fn`,
                     `ED` |-> `create_prefix_step c d explicit ctx fn`]
                    create_raw_snapshot_straight_bands) >> strip_tac >>
  `!tr. vv_location vv = SOME (slot_loc tr) ==>
    ?buf sm x exit.
      compile_alloc_buffer (type_memory_bytes ce ty) a = (buf,sm) /\
      fn_has_code sm b fn /\ lookup_block b.cs_current_bb fn.fn_blocks = SOME exit /\
      phi_prefix_length exit.bb_instructions = 0 /\
      x.vs_current_bb = sm.cs_current_bb /\ x.vs_inst_idx = LENGTH sm.cs_current_insts /\
      z.vs_inst_idx = 0 /\
      run_inst_seq (emitted_insts a sm) u = OK (x with vs_inst_idx := u.vs_inst_idx) /\
      RTC (\v w. (v.vs_current_bb <> b.cs_current_bb \/ v.vs_inst_idx <> 0) /\
                 ?ms. gas_origin_edge F explicit ctx fn v ms (OK w)) x z /\
      msS = [] /\ z.vs_gas_readings = u.vs_gas_readings` by
    (rpt strip_tac >>
     `!p ms q. create_prefix_step a b explicit ctx fn p ms q ==>
        (p.vs_current_bb <> b.cs_current_bb \/ p.vs_inst_idx <> LENGTH b.cs_current_insts) /\
        ?bb i. lookup_block p.vs_current_bb fn.fn_blocks = SOME bb /\
               get_instruction bb p.vs_inst_idx = SOME i /\ i.inst_id IN frag_ids a b /\
               gas_origin_edge F explicit ctx fn p ms (OK q)` by
       (simp[create_prefix_step_def] >> metis_tac[]) >>
     drule_all (Q.INST [`E` |-> `create_prefix_step a b explicit ctx fn`]
                 create_raw_snapshot_slot_band) >> simp[]) >>
  `vv_location vv = NONE \/ vv_location vv = SOME LocMemory \/
   vv_location vv = SOME LocCode \/ ?tr. vv_location vv = SOME (slot_loc tr)` by
    (Cases_on `vv` >> gvs[vv_location_def] >>
     rename1 `p.ptr_location <> LocCalldata` >>
     Cases_on `p.ptr_location` >> gvs[slot_loc_def] >> metis_tac[]) >>
  `msS = [] /\ z.vs_gas_readings = u.vs_gas_readings` by metis_tac[] >>
  `r.vs_gas_readings = u.vs_gas_readings` by simp[] >>
  `((vv_location vv = NONE \/ vv_location vv = SOME LocMemory \/ vv_location vv = SOME LocCode) ==>
     run_inst_seq (emitted_insts a b) u = OK (z with vs_inst_idx := u.vs_inst_idx) /\
     run_inst_seq (emitted_insts a c) u = OK (l with vs_inst_idx := u.vs_inst_idx))` by
    (qpat_assum `_ ==> run_inst_seq _ _ = _ /\ _ /\ msS = [] /\ _` mp_tac >> metis_tac[]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  rpt strip_tac >>
  qpat_assum `!tr. vv_location vv = SOME (slot_loc tr) ==> _`
    (drule_then strip_assume_tac) >>
  `fn_has_code a sm fn` by metis_tac[create_raw_snapshot_alloc_interval] >>
  qexistsl_tac [`buf`,`sm`,`x`,`exit`] >> asm_rewrite_tac[]
QED

Theorem create_raw_bytecode_header_from_replay:
  body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shadow_ctx /\
  expr_body_pre ce cx env (Call ann (CreateTarget RawCreate hs rof ks) (e::v::rest) df) es /\
  raw_bytecode_replay_at (DF,lo,dep,ctx,shadow_ctx,PG,func,shadow_func)
    tops ce cx env e es (st0,sa,a,shadow_sa,shadow_a,vv,s0,G0,tn0) /\
  expr_vv_sim_full_pre (DF,lo,dep,ctx,shadow_ctx,PG,func,shadow_func)
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
  ?p tv code G tn n.
    expr_body_pre ce cx env e es /\ expr_type e = BaseT (BytesT (Dynamic n)) /\
    LENGTH code <= n /\ n <= 49152 /\
    eval_expr cx e (es with gas_obs := gas_explicit (ms ++ later) s0.vs_gas_readings ++ tail) = (INL tv,p) /\
    p.gas_obs = gas_explicit later r.vs_gas_readings ++ tail /\
    read_result cx tv p = (INL (BytesV code),p) /\
    read_result cx tv (p with gas_obs := []) = (INL (BytesV code),p with gas_obs := []) /\
    bind (eval_exprs cx (TAKE (LENGTH rest - (if hs then 1 else 0)) rest ++
                       v :: DROP (LENGTH rest - (if hs then 1 else 0)) rest))
      (\vs. eval_create_operands cx RawCreate hs rof (MAP expr_type (e::v::rest))
        (blueprint_literal_offset cx hs (e::v::rest)) (BytesV code::vs)) p = (res,ee) /\
    valid_horizon cx st0 H p.storage_trace /\ expr_sim_inv ce cx env p /\
    eval_operand len l = SOME (n2w (LENGTH code)) /\
    local_ptrs_reserved ce a /\ fn_has_code a b func /\
    msS = [] /\ msL = [] /\ msD = [] /\ r.vs_gas_readings = u.vs_gas_readings /\
    run_inst_seq (emitted_insts b c) z = OK (l with vs_inst_idx := z.vs_inst_idx) /\
    run_inst_seq (emitted_insts c d) l = OK (r with vs_inst_idx := l.vs_inst_idx) /\
    ((vv_location vv = NONE \/ vv_location vv = SOME LocMemory \/ vv_location vv = SOME LocCode) ==>
     run_inst_seq (emitted_insts a b) u = OK (z with vs_inst_idx := u.vs_inst_idx)) /\
    (!tr. vv_location vv = SOME (slot_loc tr) ==>
      ?buf sm x exit.
        compile_alloc_buffer (type_memory_bytes ce (lowered_value_type ce e)) a = (buf,sm) /\
        fn_has_code sm b func /\ lookup_block b.cs_current_bb func.fn_blocks = SOME exit /\
        phi_prefix_length exit.bb_instructions = 0 /\
        x.vs_current_bb = sm.cs_current_bb /\ x.vs_inst_idx = LENGTH sm.cs_current_insts /\
        z.vs_inst_idx = 0 /\
        run_inst_seq (emitted_insts a sm) u = OK (x with vs_inst_idx := u.vs_inst_idx) /\
        RTC (\v w. (v.vs_current_bb <> b.cs_current_bb \/ v.vs_inst_idx <> 0) /\
                   ?ms. gas_origin_edge F (gas_explicit_sites ctx shadow_ctx) ctx func v ms (OK w)) x z) /\
    !h. valid_horizon cx st0 h p.storage_trace ==>
      gas_origin_ptr_path (DF h,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s0,G0,tn0) ms (OK u,G,tn) /\
      vv_post h ctx func ce cx e es sa a s0 (p with gas_obs := []) tv vv u /\
      vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) (p with gas_obs := []) tv vv u /\
      alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
      s0.vs_alloca_next <= u.vs_alloca_next /\
      ghost_inv_at (DF h) lo dep ce cx (p with gas_obs := []) G tn u /\
      ptr_vv_ok cx (post_value_type ce e) tv vv (p with gas_obs := []) G tn u /\
      (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
       !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
              eval_operand (vv_operand vv) u = SOME w ==>
              w2n w + type_memory_size rt <= lo /\
              (!mem. mem_agree_outside tn.t_mem u.vs_memory mem ==>
                      val_in_memory rt (BytesV code) (w2n w) mem)) /\
      (!t' op. vv = StackValue t' op /\ ~is_word_type (post_value_type ce e) ==> ptr_buf_ok ce e op G u) /\
      (!t' ptr. vv = LocatedValue t' ptr /\ ptr.ptr_location = LocMemory ==>
               ptr_buf_ok ce e ptr.ptr_operand G u) /\
      ghost_kept_at lo ce es sa G0 tn0 s0 G tn
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all (Q.INST [`later` |-> `msS ++ msL ++ msD ++ later`] create_raw_bytecode_replay_from_replay) >>
  strip_tac >- (disj1_tac >> metis_tac[]) >>
  `expr_body_pre ce cx env e es` by
    (drule exprBodyPrePropsTheory.expr_body_pre_static_facts >> strip_tac >>
     `MEM e (e::v::rest)` by simp[] >> metis_tac[create_call_operand_body_pre]) >>
  qpat_assum `!h. valid_horizon _ _ h _ ==> _ /\ _` (drule_then strip_assume_tac) >>
  `vv_location vv <> SOME LocCalldata` by
    (Cases_on `vv` >> gvs[vv_location_def] >> metis_tac[exprPtrUnwrapMarkedTheory.vv_post_not_calldata]) >>
  `fn_inst_ids_distinct func /\ MEM func ctx.ctx_functions /\ local_ptrs_reserved ce sa` by
    fs[expr_vv_sim_full_pre_def] >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[body_inv_no_phi] >>
  drule_all create_raw_header_bands >> strip_tac >>
  `local_ptrs_reserved ce a` by
    metis_tac[local_ptrs_reserved_next_var, compile_expr_ci_mono, ci_mono_def, SND] >>
  `copy_old_operand a (vv_operand vv)` by metis_tac[compile_expr_old_operand] >>
  `fn_has_code a b func` by
    metis_tac[fn_has_code_split, cs_extends_trans, ci_mono_def,
              ci_mono_compile_create_snapshot, ci_mono_emit_op, SND] >>
  `post_value_type ce e = BaseT (BytesT (Dynamic n))` by
    (irule EQ_TRANS >> qexists_tac `expr_type e` >>
     simp[post_value_type_bytestring,is_bytestring_type_def]) >>
  qabbrev_tac `obs = gas_explicit (ms ++ (msS ++ msL ++ msD ++ later)) s0.vs_gas_readings ++ tail` >>
  `expr_body_pre ce cx env e (es with gas_obs := obs)` by simp[expr_body_pre_gas_obs] >>
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := obs) =
    (INL (BytesV code),p)` by simp[bind_def] >>
  drule_all create_blueprint_raw_copy_layout >> strip_tac >>
  `LENGTH code + 32 < dimword (:256)` by
    (qpat_assum `LENGTH code <= n` mp_tac >>
     qpat_assum `n <= 49152` mp_tac >> simp[dimword_def] >> decide_tac) >>
  `eval_operand len l = SOME (n2w (LENGTH code))` by
    (suspend "snapshot_length") >>
  disj2_tac >> qexistsl_tac [`p`,`tv`,`code`,`G`,`tn`,`n`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (fs[Abbr `obs`] >> NO_TAC) >>
  metis_tac[]
QED

Resume create_raw_bytecode_header_from_replay[snapshot_length]:
  `vv_location vv = SOME LocCode ==>
     local_ptrs_reserved ce a /\
     (ce.ce_is_ctor ==> !w. eval_operand (vv_operand vv) u = SOME w ==>
        val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV code) (w2n w) u.vs_memory) /\
     w2n (n2w (buffer_allocation_base u a.cs_next_id) : bytes32) +
       32 * ((type_memory_bytes ce (vv_type vv) + 31) DIV 32) < dimword (:256)` by
    (disch_tac >> conj_tac >- first_assum ACCEPT_TAC >> conj_tac
     >- (rpt strip_tac >>
         qpat_assum `ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==> _` mp_tac >>
         simp[bodyPtrDefsTheory.mem_agree_outside_def] >> metis_tac[]) >>
     Cases_on `compile_alloc_buffer (type_memory_bytes ce (lowered_value_type ce e)) a` >>
     rename1 `_ = (buf,sm)` >> drule_all create_raw_snapshot_alloc_interval >> strip_tac >>
     drule_all create_raw_code_snapshot_site_bound >> simp[]) >>
  `!tr. vv_location vv = SOME (slot_loc tr) ==>
     ?buf sm x exit.
       compile_alloc_buffer (type_memory_bytes ce (lowered_value_type ce e)) a = (buf,sm) /\
       32 <= type_memory_bytes ce (lowered_value_type ce e) /\
       w2n (n2w (buffer_allocation_base u a.cs_next_id) : bytes32) +
         32 * ((type_memory_bytes ce (lowered_value_type ce e) + 31) DIV 32) < dimword (:256) /\
       fn_has_code sm b func /\ lookup_block b.cs_current_bb func.fn_blocks = SOME exit /\
       phi_prefix_length exit.bb_instructions = 0 /\
       x.vs_current_bb = sm.cs_current_bb /\ x.vs_inst_idx = LENGTH sm.cs_current_insts /\
       z.vs_current_bb = b.cs_current_bb /\ z.vs_inst_idx = 0 /\
       run_inst_seq (emitted_insts a sm) u = OK (x with vs_inst_idx := u.vs_inst_idx) /\
       RTC (\v w. (v.vs_current_bb <> b.cs_current_bb \/ v.vs_inst_idx <> 0) /\
                  ?ms. gas_origin_edge F (gas_explicit_sites ctx shadow_ctx) ctx func v ms (OK w)) x z /\
       run_inst_seq (emitted_insts b c) z = OK (l with vs_inst_idx := z.vs_inst_idx)` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!tr. vv_location vv = SOME (slot_loc tr) ==> _`
       (drule_then strip_assume_tac) >>
     `stmt_state_rel H ctx func ce cx (p with gas_obs := []) u` by fs[vv_post_def] >>
     drule_all create_raw_header_capacity >> strip_tac >>
     qexistsl_tac [`buf`,`sm`,`x`,`exit`] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     metis_tac[create_raw_header_slot_nonwrap]) >>
  pop_assum (mk_asm "slot_length") >>
  `((vv_location vv = NONE \/ vv_location vv = SOME LocMemory \/ vv_location vv = SOME LocCode) ==>
     run_inst_seq (emitted_insts a c) u = OK (l with vs_inst_idx := u.vs_inst_idx))` by
    (qpat_assum `_ ==> run_inst_seq (emitted_insts a b) _ = _ /\ _` mp_tac >> metis_tac[]) >>
  `((vv_location vv = NONE \/ vv_location vv = SOME LocMemory) ==> LENGTH code + 32 < dimword (:256))` by simp[] >>
  let fun consume 0 th = irule th
        | consume n th = drule_then (consume (n - 1)) th
  in consume 7 create_snapshot_length_word end >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexists_tac `gas_explicit_sites ctx shadow_ctx` >>
  gen_tac >> disch_tac >> asm "slot_length" (drule_then strip_assume_tac) >>
  qexistsl_tac [`buf`,`sm`,`x`,`z`,`exit`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
Finalise create_raw_bytecode_header_from_replay

Theorem create_raw_bytecode_header_at_cuts:
  body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shadow_ctx /\
  expr_body_pre ce cx env (Call ann (CreateTarget RawCreate hs rof ks) (e::v::rest) df) es /\
  EVERY (create_operand_completed_ok cx) (create_operand_order RawCreate hs (e::v::rest)) /\
  expr_vv_sim_full_pre (DF,lo,dep,ctx,shadow_ctx,PG,func,shadow_func)
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
  ?p tv code G tn n.
    expr_body_pre ce cx env e es /\ expr_type e = BaseT (BytesT (Dynamic n)) /\
    LENGTH code <= n /\ n <= 49152 /\
    eval_expr cx e (es with gas_obs := gas_explicit (ms ++ later) s0.vs_gas_readings ++ tail) = (INL tv,p) /\
    p.gas_obs = gas_explicit later r.vs_gas_readings ++ tail /\
    read_result cx tv p = (INL (BytesV code),p) /\
    read_result cx tv (p with gas_obs := []) = (INL (BytesV code),p with gas_obs := []) /\
    bind (eval_exprs cx (TAKE (LENGTH rest - (if hs then 1 else 0)) rest ++
                       v :: DROP (LENGTH rest - (if hs then 1 else 0)) rest))
      (\vs. eval_create_operands cx RawCreate hs rof (MAP expr_type (e::v::rest))
        (blueprint_literal_offset cx hs (e::v::rest)) (BytesV code::vs)) p = (res,ee) /\
    valid_horizon cx st0 H p.storage_trace /\ expr_sim_inv ce cx env p /\
    eval_operand len l = SOME (n2w (LENGTH code)) /\
    local_ptrs_reserved ce a /\ fn_has_code a b func /\
    msS = [] /\ msL = [] /\ msD = [] /\ r.vs_gas_readings = u.vs_gas_readings /\
    run_inst_seq (emitted_insts b c) z = OK (l with vs_inst_idx := z.vs_inst_idx) /\
    run_inst_seq (emitted_insts c d) l = OK (r with vs_inst_idx := l.vs_inst_idx) /\
    ((vv_location vv = NONE \/ vv_location vv = SOME LocMemory \/ vv_location vv = SOME LocCode) ==>
     run_inst_seq (emitted_insts a b) u = OK (z with vs_inst_idx := u.vs_inst_idx)) /\
    (!tr. vv_location vv = SOME (slot_loc tr) ==>
      ?buf sm x exit.
        compile_alloc_buffer (type_memory_bytes ce (lowered_value_type ce e)) a = (buf,sm) /\
        fn_has_code sm b func /\ lookup_block b.cs_current_bb func.fn_blocks = SOME exit /\
        phi_prefix_length exit.bb_instructions = 0 /\
        x.vs_current_bb = sm.cs_current_bb /\ x.vs_inst_idx = LENGTH sm.cs_current_insts /\
        z.vs_inst_idx = 0 /\
        run_inst_seq (emitted_insts a sm) u = OK (x with vs_inst_idx := u.vs_inst_idx) /\
        RTC (\v w. (v.vs_current_bb <> b.cs_current_bb \/ v.vs_inst_idx <> 0) /\
                   ?ms. gas_origin_edge F (gas_explicit_sites ctx shadow_ctx) ctx func v ms (OK w)) x z) /\
    !h. valid_horizon cx st0 h p.storage_trace ==>
      gas_origin_ptr_path (DF h,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s0,G0,tn0) ms (OK u,G,tn) /\
      vv_post h ctx func ce cx e es sa a s0 (p with gas_obs := []) tv vv u /\
      vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) (p with gas_obs := []) tv vv u /\
      alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
      s0.vs_alloca_next <= u.vs_alloca_next /\
      ghost_inv_at (DF h) lo dep ce cx (p with gas_obs := []) G tn u /\
      ptr_vv_ok cx (post_value_type ce e) tv vv (p with gas_obs := []) G tn u /\
      (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
       !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
              eval_operand (vv_operand vv) u = SOME w ==>
              w2n w + type_memory_size rt <= lo /\
              (!mem. mem_agree_outside tn.t_mem u.vs_memory mem ==>
                      val_in_memory rt (BytesV code) (w2n w) mem)) /\
      (!t' op. vv = StackValue t' op /\ ~is_word_type (post_value_type ce e) ==> ptr_buf_ok ce e op G u) /\
      (!t' ptr. vv = LocatedValue t' ptr /\ ptr.ptr_location = LocMemory ==>
               ptr_buf_ok ce e ptr.ptr_operand G u) /\
      ghost_kept_at lo ce es sa G0 tn0 s0 G tn
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all raw_bytecode_replay_at_of_completed >> disch_tac >>
  mp_tac (SPEC_ALL create_raw_bytecode_header_from_replay) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >>
  disch_then ACCEPT_TAC
QED
