Theory createSizeBlueprintRawScalarsMods
Ancestors
  createSizeBlueprintRawScalars createExprSizeExitDefsMods
  gasShadowCompileBase
  abiEncoderProps e2eDefs exprSimFullBundleProps fragExec fragGasOrigin gasExplicitSites
  gasSummary venomExecSemantics venomInst venomState vyperState relation list words
  createMarkedPath pair bodyFullIfExpReach arithmetic exprLowering stmtLoweringMono
  vfmConstants loweringShapeRules compileEnv exprLoweringProps exprBodyPreProps
  vyperStorageTrace bodyMemoryDefs freshWrites rich_list exprSimHypsDefs
  vyperTypeExprSoundness exprSimHyps bodyPtrDefs loweringPosts context vyperAST
  vyperStorageFootprint vyperTyping vyperValue ghostPcTransportPtr integer_word
  aggregateEvaluatedLayout loweringStateRelDefs createSizeByteLength createBlueprintRawCopyMods
  bodyFullGhostFrame assignTuplePtrLoadStep augAssignFullLoadFrame contextRawReachable
  stateFrame ptrDiscipline stmtReasonMemory emitHelperProps bodyPtrMakeArrayEmission
  venomInstProofs1 gasEvents bodySim loweringShapeDefs createExprSizeExitDefs
  createSizePrefixReplayMods createSizeObservedPrefix createCtorSegmentArrival
  createSizeBlueprintKeywordReplayMods

(* A retained operand is replayed through its unwrap as one scalar read. *)

Theorem blueprint_raw_nonword_tag_mods[local]:
  expr_body_pre_mods mods ce cx env e p /\ expr_type e = BaseT (BytesT (Dynamic k)) /\
  compile_expr ce (expr_type e) e ca = (vv,cm) ==>
  ~is_word_type (vv_type vv)
Proof
  cheat
QED

Theorem blueprint_raw_retained_at_cut_mods:
  contract_inv mods exps ctx ce cx /\
  module_body_inv mods src tops ce cx /\ shadow_body_inv_mods mods exps ctx shctx /\
  expr_body_pre_mods mods ce cx env e p /\ create_operand_completed_ok_mods mods exps cx e /\
  expr_type e = BaseT (BytesT (Dynamic k)) /\ ~exprs_can_mutate ce later /\
  eval_operand target_op s = SOME aw /\ (!x. target_op = Var x ==> not_fresh_at ca x) /\
  local_ptrs_reserved ce ca /\ (!h. dead_lo_ok_mods h (DF h) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  return_buf_frame d ce ca s /\ alloca_history fnc s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!f i z. frag_reachable ctx fnc s f i z ==> dalloca_fmp_headroom i z) /\
  (!h. valid_horizon cx st0 h p.storage_trace ==>
    stmt_state_rel h ctx fnc ce cx p s /\
    immutable_frame_mods fnc ce cx p s /\ storage_well_formed_on cx p (FST h) /\
    ghost_inv_at_mods (DF h) lo d ce cx p G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = ca.cs_current_bb /\
  s.vs_inst_idx = LENGTH ca.cs_current_insts /\
  compile_expr ce (expr_type e) e ca = (vv,cm) /\
  compile_snapshot_vv ce (exprs_can_mutate ce later) vv cm = (saved,cs) /\
  unwrap_value ce saved cs = (raw_op,cu) /\
  compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) sca = (vv,scm) /\
  compile_snapshot_vv ce (exprs_can_mutate ce (MAP gas_shadow_expr later)) vv scm = (ssaved,scs) /\
  unwrap_value ce ssaved scs = (raw_op,scu) /\
  expr_sim_full_code (ctx,shctx,fnc,shfnc) (ca,cu,sca,scu) /\
  emit_op MLOAD [raw_op] cu = (len,cl) /\ fn_has_code cu cl fnc /\
  create_expr_prefix ca cm (gas_explicit_sites ctx shctx) ctx fnc s mc m /\
  create_expr_prefix cm cs (gas_explicit_sites ctx shctx) ctx fnc m ms v /\
  create_expr_prefix cs cu (gas_explicit_sites ctx shctx) ctx fnc v mu u /\
  u.vs_current_bb = cu.cs_current_bb /\ u.vs_inst_idx = LENGTH cu.cs_current_insts /\
  (!v. storage_trace_frame (kont v)) /\
  bind (bind (eval_expr cx e) (read_result cx)) kont p = (res,out) /\
  valid_horizon cx st0 H out.storage_trace /\
  p.gas_obs = gas_explicit (mc ++ (ms ++ (mu ++ rest))) s.vs_gas_readings ++ tail ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt_mods mods err) \/
  ?bs q G' tn'.
    bind (eval_expr cx e) (read_result cx) p = (INL (BytesV bs),q) /\
    kont (BytesV bs) q = (res,out) /\ valid_horizon cx st0 H q.storage_trace /\
    q.gas_obs = gas_explicit rest u.vs_gas_readings ++ tail /\
    expr_val_rel cx (BaseT (BytesT (Dynamic k))) (BytesV bs) raw_op u /\
    eval_operand target_op u = SOME aw /\ (!x. target_op = Var x ==> not_fresh_at cu x) /\
    expr_sim_inv_mods mods ce cx env q /\ local_ptrs_reserved ce cu /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at cu x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cu x) /\
    return_buf_frame d ce cu u /\ alloca_history fnc u /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    (!f i z. frag_reachable ctx fnc u f i z ==> dalloca_fmp_headroom i z) /\
    (!h. valid_horizon cx st0 h q.storage_trace ==>
      stmt_state_rel h ctx fnc ce cx q u /\
      immutable_frame_mods fnc ce cx q u /\ storage_well_formed_on cx q (FST h) /\
      ghost_inv_at_mods (DF h) lo d ce cx q G' tn' u) /\
    ~u.vs_halted /\ u.vs_current_bb = cu.cs_current_bb /\
    u.vs_inst_idx = LENGTH cu.cs_current_insts
Proof
  cheat
QED

Theorem blueprint_raw_load_add_frame_mods:
  fn_has_code cu cprep fn /\ cprep.cs_current_bb = cu.cs_current_bb /\
  cprep.cs_current_insts = cu.cs_current_insts ++ emitted_insts cu cprep /\
  EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts cu cprep) /\
  a.vs_current_bb = cu.cs_current_bb /\ a.vs_inst_idx = LENGTH cu.cs_current_insts /\
  u.vs_inst_idx = LENGTH cprep.cs_current_insts /\ cu.cs_next_var <= cprep.cs_next_var /\
  state_frame u = state_frame (a with vs_inst_idx := u.vs_inst_idx) /\
  (!x. not_fresh_at cu x ==> lookup_var x u = lookup_var x a) /\
  local_ptrs_reserved ce cu /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at cu x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cu x) /\
  return_buf_frame d ce cu a /\ alloca_history fn a /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp a) /\
  (!h. valid_horizon cx st0 h p.storage_trace ==>
    stmt_state_rel h ctx fn ce cx p a /\
    immutable_frame_mods fn ce cx p a /\ ghost_inv_at_mods (DF h) lo d ce cx p G tn a) ==>
  return_buf_frame d ce cprep u /\ alloca_history fn u /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  (!h. valid_horizon cx st0 h p.storage_trace ==>
    stmt_state_rel h ctx fn ce cx p u /\
    immutable_frame_mods fn ce cx p u /\ ghost_inv_at_mods (DF h) lo d ce cx p G tn u)
Proof
  cheat
QED

Theorem blueprint_raw_finish_at_cut_mods:
  expr_type e = BaseT (BytesT (Dynamic k)) /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic k))) =
    SOME (BaseTV (BytesT (Dynamic k))) /\
  compile_expr ce (expr_type e) e ca = (vv,cm) /\
  compile_snapshot_vv ce (exprs_can_mutate ce later) vv cm = (saved,cs) /\
  unwrap_value ce saved cs = (raw_op,cu) /\
  compile_create_blueprint_args compile_expr ce T later [e] ca = ((data,len),cprep) /\
  expr_val_rel cx (BaseT (BytesT (Dynamic k))) (BytesV bs) raw_op u /\
  eval_operand target_op u = SOME aw /\
  (!x. target_op = Var x ==> not_fresh_at cu x) /\
  expr_sim_inv_mods mods ce cx env q /\
  local_ptrs_reserved ce cu /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at cu x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cu x) /\
  return_buf_frame d ce cu u /\ alloca_history fnc u /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  (!f i z. frag_reachable ctx fnc u f i z ==> dalloca_fmp_headroom i z) /\
  (!h. valid_horizon cx st0 h q.storage_trace ==>
    stmt_state_rel h ctx fnc ce cx q u /\
    immutable_frame_mods fnc ce cx q u /\ storage_well_formed_on cx q (FST h) /\
    ghost_inv_at_mods (DF h) lo d ce cx q G tn u) /\
  ~u.vs_halted /\ u.vs_current_bb = cu.cs_current_bb /\
  u.vs_inst_idx = LENGTH cu.cs_current_insts /\
  emit_op MLOAD [raw_op] cu = (len,cl) /\
  emit_op ADD [raw_op;Lit 32w] cl = (data,cprep) /\ fn_has_code cu cprep fnc /\
  b.vs_current_bb = cl.cs_current_bb /\ b.vs_inst_idx = LENGTH cl.cs_current_insts /\
  t.vs_current_bb = cprep.cs_current_bb /\ t.vs_inst_idx = LENGTH cprep.cs_current_insts /\
  create_expr_prefix cu cl explicit ctx fnc u ml b /\
  create_expr_prefix cl cprep explicit ctx fnc b ma t /\
  (!bb. MEM bb fnc.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  q.gas_obs = gas_explicit (ml ++ ma ++ rest) u.vs_gas_readings ++ tail ==>
  eval_operand len t = SOME (n2w (LENGTH bs)) /\
  (!x. len = Var x ==> not_fresh_at cprep x) /\
  eval_operand target_op t = SOME aw /\
  (!x. target_op = Var x ==> not_fresh_at cprep x) /\
  expr_sim_inv_mods mods ce cx env q /\
  local_ptrs_reserved ce cprep /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at cprep x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cprep x) /\
  return_buf_frame d ce cprep t /\ alloca_history fnc t /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  (!f i z. frag_reachable ctx fnc t f i z ==> dalloca_fmp_headroom i z) /\
  (!h. valid_horizon cx st0 h q.storage_trace ==>
    stmt_state_rel h ctx fnc ce cx q t /\
    immutable_frame_mods fnc ce cx q t /\ storage_well_formed_on cx q (FST h) /\
    ghost_inv_at_mods (DF h) lo d ce cx q G tn t) /\
  ~t.vs_halted /\ t.vs_current_bb = cprep.cs_current_bb /\
  t.vs_inst_idx = LENGTH cprep.cs_current_insts /\
  q.gas_obs = gas_explicit rest t.vs_gas_readings ++ tail
Proof
  cheat
QED
