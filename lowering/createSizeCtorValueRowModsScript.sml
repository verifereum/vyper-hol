Theory createSizeCtorValueRowMods
Ancestors
  createSizeCtorValueRow createExprSizeExitDefsMods
  gasShadowCompileBase
  abiEncoderProps e2eDefs exprSimFullBundleProps fragExec fragGasOrigin fragGasOriginPtr
  gasExplicitSites gasSummary s1PrefixDefs venomExecSemantics venomState vyperState relation
  list words createMarkedPath pair bodyFullIfExpReach arithmetic exprLowering
  stmtLoweringMono vfmConstants compileEnv exprLoweringProps exprSimSource vyperStorageTrace
  fragGasOriginPtrExec bodyMemoryDefs rich_list exprSimHypsDefs vyperTypeSystem exprSimHyps
  bodyPtrDefs loweringPosts context vyperAST vyperStorageFootprint vyperTyping vyperValue
  integer_word valueEncoding createCtorPrivateSnapshotMods createCtorSegmentArrival
  bodyFullExtCallPosList bodyFullExtCallPosAggregate abiEncodeArgsSim abiEncodeArgsCase
  exprSimMemorySource bodyFullHashKeccakFixed aggregateEvaluatedLayout
  exprSimIfExpWidenedPhysicalType exprSimSubscriptArrayCompose loweringStateRelDefs
  exprSimMemDefs ptrDiscipline bodySim createExprSizeExitDefs createSizePrefixReplayMods
  createSizeCopyReplayMods createSizeBlueprintKeywordReplayMods createSizeRawReplayMods

(* Visit the calls in the original suffix, while carrying their reached
   source states. The continuation is kept under its actual bind. *)

Theorem blueprint_ctor_source_walk_mods:
  !mods n i p k.
    i + n = LENGTH es /\ P i p /\
    bind (eval_exprs cx (DROP i es)) k p = (res,out) /\
    (!vs. storage_trace_frame (k vs)) /\
    (!j q l. j < LENGTH es /\ P j q /\ (!v. storage_trace_frame (l v)) /\
       bind (bind (eval_expr cx (EL j es)) (read_result cx)) l q = (res,out) ==>
       (?err. res = INR (Error err) /\ unspecified_behaviour_exempt_mods mods err) \/
       ?v q'. bind (eval_expr cx (EL j es)) (read_result cx) q = (INL v,q') /\
              l v q' = (res,out) /\ P (SUC j) q') ==>
    (?err. res = INR (Error err) /\ unspecified_behaviour_exempt_mods mods err) \/
    ?vs E. E i = p /\ LENGTH vs = n /\
       eval_exprs cx (DROP i es) p = (INL vs,E (LENGTH es)) /\
       k vs (E (LENGTH es)) = (res,out) /\
       (!j. i <= j /\ j <= LENGTH es ==> P j (E j)) /\
       (!j. i <= j /\ j < LENGTH es ==>
         bind (eval_expr cx (EL j es)) (read_result cx) (E j) =
           (INL (EL (j-i) vs),E (SUC j)))
Proof
  cheat
QED

Theorem blueprint_ctor_complete_mods:
  gas_completed_operand_mods (DF,lo,explicit,ctx,func,PG)
    mods cx st0 a b source (p,s,G,tn) Q /\
  create_expr_prefix a b explicit ctx func s marks t /\
  t.vs_current_bb = b.cs_current_bb /\ t.vs_inst_idx = LENGTH b.cs_current_insts /\
  source p = (rr,q) /\ valid_horizon cx st0 H q.storage_trace /\
  p.gas_obs = gas_explicit marks s.vs_gas_readings ++ suffix ==>
  (?err. rr = INR (Error err) /\ unspecified_behaviour_exempt_mods mods err) \/
  ?G' tn'. q.gas_obs = suffix /\
    !h. valid_horizon cx st0 h q.storage_trace ==>
      gas_origin_ptr_path (DF h,lo,explicit,ctx,func,PG) (s,G,tn) marks (OK t,G',tn') /\
      Q h rr (q with gas_obs := []) G' tn' t
Proof
  cheat
QED

Theorem blueprint_ctor_vv_row_mods:
  contract_inv mods exps ctx ce cx /\
  module_body_inv mods src tops ce cx /\ shadow_body_inv_mods mods exps ctx shctx /\
  expr_body_pre_mods mods ce cx env e p /\ create_operand_completed_ok_mods mods exps cx e /\
  ~is_word_type (lowered_value_type ce e) /\
  compile_expr ce (expr_type e) e a = (vv,m) /\
  compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) sha = (vv,shm) /\
  expr_sim_full_code (ctx,shctx,func,shfunc) (a,m,sha,shm) /\
  compile_snapshot_vv ce (exprs_can_mutate ce xs)
    (ext_call_arg_value (lowered_value_type ce e) vv) m = (saved,b) /\
  local_ptrs_reserved ce a /\ (!h. dead_lo_ok_mods h (DF h) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  return_buf_frame d ce a s /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!f i z. frag_reachable ctx func s f i z ==> dalloca_fmp_headroom i z) /\
  (!h. valid_horizon cx st0 h p.storage_trace ==>
     stmt_state_rel h ctx func ce cx p s /\
     immutable_frame_mods func ce cx p s /\ storage_well_formed_on cx p (FST h) /\
     ghost_inv_at_mods (DF h) lo d ce cx p G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  create_expr_prefix a m (gas_explicit_sites ctx shctx) ctx func s chunk mid /\
  mid.vs_current_bb = m.cs_current_bb /\ mid.vs_inst_idx = LENGTH m.cs_current_insts /\
  create_expr_prefix m b (gas_explicit_sites ctx shctx) ctx func mid snap t /\
  t.vs_current_bb = b.cs_current_bb /\ t.vs_inst_idx = LENGTH b.cs_current_insts /\
  (exprs_can_mutate ce xs ==>
    fn_has_code m b func /\
    (?j. ctor_segment_fetch func t = SOME j /\ j.inst_opcode <> PHI /\
         b.cs_next_id <= j.inst_id) /\
    (gas_origin_path T (gas_explicit_sites ctx shctx) ctx func mid [] (OK t) ==> snap = [])) /\
  bind (eval_expr cx e) (read_result cx) p = (rr,q) /\
  valid_horizon cx st0 H q.storage_trace /\
  p.gas_obs = gas_explicit (chunk ++ (snap ++ rest)) s.vs_gas_readings ++ tail ==>
  (?err. rr = INR (Error err) /\ unspecified_behaviour_exempt_mods mods err) \/
  ?v raw Gm tm tv ann Gt tt.
    rr = INL v /\ eval_expr cx e p = (INL raw,q) /\ read_result cx raw q = (INL v,q) /\
    evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME ann /\
    arg_type_fits (lowered_value_type ce e) (expr_type e) /\
    value_has_type tv v /\ value_has_type ann v /\
    (!h. valid_horizon cx st0 h q.storage_trace ==>
       vv_post_mods h ctx func ce cx e p a m s (q with gas_obs := []) raw vv mid /\
       vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e)
         (q with gas_obs := []) raw vv mid /\
       ptr_vv_ok cx (post_value_type ce e) raw vv (q with gas_obs := []) Gm tm mid /\
       alloca_history func mid /\ s.vs_alloca_next <= mid.vs_alloca_next /\
       ghost_inv_at_mods (DF h) lo d ce cx (q with gas_obs := []) Gm tm mid /\
       ghost_kept_at lo ce p a G tn s Gm tm /\
       (!tag op. vv = StackValue tag op /\ ~is_word_type (post_value_type ce e) ==>
         ptr_buf_ok ce e op Gm mid) /\
       (!tag p0. vv = LocatedValue tag p0 /\ p0.ptr_location = LocMemory ==>
         ptr_buf_ok ce e p0.ptr_operand Gm mid) /\
       (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
         ?val. read_result cx raw (q with gas_obs := []) = (INL val,q with gas_obs := []) /\
           !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
             eval_operand (vv_operand vv) mid = SOME w ==>
             w2n w + type_memory_size rt <= lo /\
             (!mem. mem_agree_outside tm.t_mem mid.vs_memory mem ==>
                val_in_memory rt val (w2n w) mem))) /\
    q.gas_obs = gas_explicit rest t.vs_gas_readings ++ tail /\
    expr_sim_inv_mods mods ce cx env q /\ return_buf_frame d ce b t /\ alloca_history func t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!f i z. frag_reachable ctx func t f i z ==> dalloca_fmp_headroom i z) /\
    ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
    t.vs_inst_idx = LENGTH b.cs_current_insts /\
    (!h. valid_horizon cx st0 h q.storage_trace ==>
      stmt_state_rel h ctx func ce cx q t /\
      immutable_frame_mods func ce cx q t /\ storage_well_formed_on cx q (FST h) /\
      ghost_inv_at_mods (DF h) lo d ce cx q Gt tt t)
Proof
  cheat
QED
