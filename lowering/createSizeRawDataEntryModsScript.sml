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
  createSizeRawHeaderReplayMods

(* Forget the mark accumulator, keeping the same target execution. *)

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
  cheat
QED
