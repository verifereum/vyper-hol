Theory createSizeRawHeaderReplayMods
Ancestors
  createSizeRawHeaderReplay createExprSizeExitDefsMods
  gasShadowCompileBase
  abiEncoderProps e2eDefs exprSimFullBundleProps fragExec fragGasOrigin gasExplicitSites
  gasSummary s1PrefixDefs venomExecSemantics venomInst venomState vyperCreate vyperState
  relation list words pair bodyFullIfExpReach arithmetic exprLowering vfmConstants
  compileEnv exprLoweringProps exprBodyPreProps exprSimCopy exprSimSource rich_list
  exprSimHypsDefs bodyPtrDefs loweringPosts context createSizeSnapshotLengthMods vyperAST
  vyperStorageFootprint vyperValue integer_word valueEncoding loweringStateRelDefs
  exprSimMemDefs ptrDiscipline createSizeRawStraightBands createSizeRawSlotBand
  createSizeRawCodeSiteBoundMods createSizeRawHeaderGeometryMods reasonEndpointResourcesPtr
  createBlueprintRawCopyLayoutMods bodySim createExprSizeExitDefs createSizePrefixReplayMods
  createSizeRawReplayMods createSizeOperandPreMods

Theorem create_raw_bytecode_header_at_cuts_mods:
  contract_inv mods exps ctx ce cx /\
  module_body_inv mods src tops ce cx /\ shadow_body_inv_mods mods exps ctx shadow_ctx /\
  expr_body_pre_mods mods ce cx env (Call ann (CreateTarget RawCreate hs rof ks) (e::v::rest) df) es /\
  EVERY (create_operand_completed_ok_mods mods exps cx) (create_operand_order RawCreate hs (e::v::rest)) /\
  expr_vv_sim_full_pre_mods (DF,lo,dep,ctx,shadow_ctx,PG,func,shadow_func)
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
  ?p tv code G tn n.
    expr_body_pre_mods mods ce cx env e es /\ expr_type e = BaseT (BytesT (Dynamic n)) /\
    LENGTH code <= n /\ n <= 49152 /\
    eval_expr cx e (es with gas_obs := gas_explicit (ms ++ later) s0.vs_gas_readings ++ tail) = (INL tv,p) /\
    p.gas_obs = gas_explicit later r.vs_gas_readings ++ tail /\
    read_result cx tv p = (INL (BytesV code),p) /\
    read_result cx tv (p with gas_obs := []) = (INL (BytesV code),p with gas_obs := []) /\
    bind (eval_exprs cx (TAKE (LENGTH rest - (if hs then 1 else 0)) rest ++
                       v :: DROP (LENGTH rest - (if hs then 1 else 0)) rest))
      (\vs. eval_create_operands cx RawCreate hs rof (MAP expr_type (e::v::rest))
        (blueprint_literal_offset cx hs (e::v::rest)) (BytesV code::vs)) p = (res,ee) /\
    valid_horizon cx st0 H p.storage_trace /\ expr_sim_inv_mods mods ce cx env p /\
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
      vv_post_mods h ctx func ce cx e es sa a s0 (p with gas_obs := []) tv vv u /\
      vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) (p with gas_obs := []) tv vv u /\
      alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
      s0.vs_alloca_next <= u.vs_alloca_next /\
      ghost_inv_at_mods (DF h) lo dep ce cx (p with gas_obs := []) G tn u /\
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
  cheat
QED
