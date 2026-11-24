Theory entryCreateBlueprintRawOwnerPayload
Ancestors
  createSizeBlueprintRawScalars createSizeBlueprintRawCopyReplay
  createSizeBlueprintKeywordReplay entryCreateRawArgExtent entryCreateFocusSpec
  bodyFullPreds createSizeOperandPre exprBodyPreProps exprSimHyps
  createSizeCopyReplay exprSimAccounts bodyFullIfExpReach gasShadowCompileBase
  exprSimFullBundleProps createExprSizeExitDefs s1PrefixDefs fragExec
  exprLowering loweringPosts vyperCreate vyperTyping vyperValue vyperAST
  vyperState vyperStorageTrace vyperStorageFootprint bodySim vyperTypeSystem
  list rich_list exprLoweringProps compileEnv bodyPtrDefs ptrDiscipline
  loweringStateRelDefs gasSummary gasExplicitSites venomState

Theorem blueprint_raw_payload_source[local]:
  expr_body_pre ce cx env
    (Call ann (CreateTarget (CreateFromBlueprint T) hs rof ks) args df) entry /\
  args = target::amount::((if hs then [salt] else []) ++ off::ctors) /\
  e = HD ctors /\ expr_sim_inv ce cx env p ==>
  ?cap. ctors = [e] /\ expr_type e = BaseT (BytesT (Dynamic cap)) /\
    expr_body_pre ce cx env e p /\
    evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic cap))) =
      SOME (BaseTV (BytesT (Dynamic cap)))
Proof
  strip_tac >>
  `?cap. ctors = [e] /\ expr_type e = BaseT (BytesT (Dynamic cap))` by
    (drule expr_body_pre_static_facts >> strip_tac >>
     Cases_on `hs` >> fs[well_typed_expr_def,create_arg_types_ok_def,MAP_EQ_CONS] >>
     gvs[] >> metis_tac[]) >>
  qpat_x_assum `e = HD ctors` kall_tac >>
  `expr_body_pre ce cx env e p` by
    (irule create_call_operand_body_pre >> conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _` (irule_at Any) >> simp[]) >>
  `well_typed_expr env e` by
    (qpat_assum `expr_body_pre ce cx env e p`
       (mp_then Any strip_assume_tac expr_body_pre_static_facts) >> simp[]) >>
  qexists_tac `cap` >> simp[] >>
  drule_all expr_sim_inv_type_evaluates >>
  simp[evaluate_type_def] >> reverse IF_CASES_TAC >> simp[]
QED

(* The selected argument is either read through unwrap or first replayed as a
   VV and privately copied. Both branches identify the same source bytes at
   the pre-MLOAD state, without asking for a completedness law at other entries. *)
Theorem blueprint_agreed_raw_payload:
  body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shctx /\
  expr_body_pre ce cx env (Call ann (CreateTarget (CreateFromBlueprint T) hs rof ks) args df) entry /\
  args = target::amount::((if hs then [salt] else []) ++ off::ctors) /\
  e = HD ctors /\ later = amount::((if hs then [salt] else []) ++ [off]) /\
  body_const_cells_agree [(NONE,tops)] cx env p /\
  (expr_body_pre ce cx env e p /\ body_const_cells_agree [(NONE,tops)] cx env p /\
    expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,fnc,shfnc) ce cx (expr_type e) e p
      (st0,ca,cu,sca,scu,raw_op,s,Gi,ti) ==>
    gas_completed_operand (DF,lo,gas_explicit_sites ctx shctx,ctx,fnc,PG)
      tops cx st0 ca cu (bind (eval_expr cx e) (read_result cx)) (p,s,Gi,ti)
      (expr_sim_full_post (DF,lo,d,ctx,fnc) ce cx e (p,ca,cu,s,raw_op,Gi,ti))) /\
  (expr_body_pre ce cx env e p /\ body_const_cells_agree [(NONE,tops)] cx env p /\
    expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,([]:(num # num) option list),fnc,shfnc) ce cx (expr_type e) e p
      (st0,ca,cm,sca,scm,vv,s,Gi,ti) ==>
    gas_completed_operand (DF,lo,gas_explicit_sites ctx shctx,ctx,fnc,[])
      tops cx st0 ca cm (eval_expr cx e) (p,s,Gi,ti)
      (create_operand_vv_post (DF,lo,d,ctx,fnc) ce cx e (p,ca,cm,s,vv,Gi,ti))) /\
  eval_operand target_op s = SOME aw /\ (!x. target_op = Var x ==> not_fresh_at ca x) /\
  expr_sim_inv ce cx env p /\
  local_ptrs_reserved ce ca /\ (!h. dead_lo_ok h (DF h) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  return_buf_frame d ce ca s /\ alloca_history fnc s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!f i z. frag_reachable ctx fnc s f i z ==> dalloca_fmp_headroom i z) /\
  (!h. valid_horizon cx st0 h p.storage_trace ==>
    stmt_state_rel h ctx fnc ce cx p s /\ storage_well_formed_on cx p (FST h) /\
    ghost_inv_at (DF h) lo d ce cx p Gi ti s) /\
  ~s.vs_halted /\ s.vs_current_bb = ca.cs_current_bb /\ s.vs_inst_idx = LENGTH ca.cs_current_insts /\
  compile_expr ce (expr_type e) e ca = (vv,cm) /\
  compile_snapshot_vv ce (exprs_can_mutate ce later) vv cm = (saved,cs) /\
  unwrap_value ce saved cs = (raw_op,cu) /\
  compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) sca = (vv,scm) /\
  compile_snapshot_vv ce (exprs_can_mutate ce (MAP gas_shadow_expr later)) vv scm = (ssaved,scs) /\
  unwrap_value ce ssaved scs = (raw_op,scu) /\
  expr_sim_full_code (ctx,shctx,fnc,shfnc) (ca,cm,sca,scm) /\
  expr_sim_full_code (ctx,shctx,fnc,shfnc) (ca,cu,sca,scu) /\
  fn_has_code cm cs fnc /\ fn_has_code cu cprep fnc /\
  emit_op MLOAD [raw_op] cu = (len,cl) /\ emit_op ADD [raw_op;Lit 32w] cl = (data,cprep) /\
  create_expr_prefix ca cm (gas_explicit_sites ctx shctx) ctx fnc s mc m /\
  m.vs_current_bb = cm.cs_current_bb /\ m.vs_inst_idx = LENGTH cm.cs_current_insts /\
  create_expr_prefix cm cs (gas_explicit_sites ctx shctx) ctx fnc m ms r /\
  r.vs_current_bb = cs.cs_current_bb /\ r.vs_inst_idx = LENGTH cs.cs_current_insts /\
  create_expr_prefix cs cu (gas_explicit_sites ctx shctx) ctx fnc r mu u /\
  u.vs_current_bb = cu.cs_current_bb /\ u.vs_inst_idx = LENGTH cu.cs_current_insts /\
  create_expr_prefix cu cl (gas_explicit_sites ctx shctx) ctx fnc u ml b /\
  b.vs_current_bb = cl.cs_current_bb /\ b.vs_inst_idx = LENGTH cl.cs_current_insts /\
  create_expr_prefix cl cprep (gas_explicit_sites ctx shctx) ctx fnc b ma t /\
  t.vs_current_bb = cprep.cs_current_bb /\ t.vs_inst_idx = LENGTH cprep.cs_current_insts /\
  bind (eval_exprs cx (ctors ++ later))
    (\vs. eval_create_operands cx (CreateFromBlueprint T) hs rof
      (MAP expr_type args) (blueprint_literal_offset cx hs args) (av::vs)) p = (res,out) /\
  valid_horizon cx st0 H out.storage_trace /\
  p.gas_obs = gas_explicit (mc ++ (ms ++ (mu ++ (ml ++ ma ++ rest)))) s.vs_gas_readings ++ tail ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
  ?bs q G tn.
    ctors = [e] /\
    bind (eval_exprs cx later)
      (\kvs. eval_create_operands cx (CreateFromBlueprint T) hs rof
        (MAP expr_type args) (blueprint_literal_offset cx hs args) (av::BytesV bs::kvs)) q = (res,out) /\
    valid_horizon cx st0 H q.storage_trace /\
    eval_operand len t = SOME (n2w (LENGTH bs)) /\
    (!x. len = Var x ==> not_fresh_at cprep x) /\
    (!z. (!x w. not_fresh_at cprep x /\ lookup_var x t = SOME w ==> lookup_var x z = SOME w) /\
      z.vs_labels = t.vs_labels ==>
      eval_operand len z = SOME (n2w (LENGTH bs)) /\
      w2n (n2w (LENGTH bs) : bytes32) < 2 ** 64) /\
    eval_operand target_op t = SOME aw /\
    (!x. target_op = Var x ==> not_fresh_at cprep x) /\
    expr_sim_inv ce cx env q /\ body_const_cells_agree [(NONE,tops)] cx env q /\
    local_ptrs_reserved ce cprep /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at cprep x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cprep x) /\
    return_buf_frame d ce cprep t /\ alloca_history fnc t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!f i z. frag_reachable ctx fnc t f i z ==> dalloca_fmp_headroom i z) /\
    (!h. valid_horizon cx st0 h q.storage_trace ==>
      stmt_state_rel h ctx fnc ce cx q t /\ storage_well_formed_on cx q (FST h) /\
      ghost_inv_at (DF h) lo d ce cx q G tn t) /\
    ~t.vs_halted /\ t.vs_current_bb = cprep.cs_current_bb /\
    t.vs_inst_idx = LENGTH cprep.cs_current_insts /\
    q.gas_obs = gas_explicit rest t.vs_gas_readings ++ tail
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all blueprint_raw_payload_source >> strip_tac >>
  qpat_x_assum `e = HD ctors` kall_tac >>
  `fn_has_code cu cl fnc` by
    metis_tac[fn_has_code_split,exprSimAccountsTheory.emit_op_extends_next_var] >>
  `!bb. MEM bb fnc.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (gen_tac >> disch_tac >>
     `MEM fnc ctx.ctx_functions` by fs[expr_sim_full_code_def] >>
     drule_all body_inv_no_phi >> simp[]) >>
  `compile_create_blueprint_args compile_expr ce T later [e] ca = ((data,len),cprep)` by
    (qpat_x_assum `later = _` kall_tac >> qpat_x_assum `expr_type e = _` kall_tac >>
     simp[compile_create_blueprint_args_def,comp_bind_def,comp_return_def]) >>
  qabbrev_tac `kont = \v. bind (eval_exprs cx later)
    (\vs. eval_create_operands cx (CreateFromBlueprint T) hs rof
      (MAP expr_type args) (blueprint_literal_offset cx hs args) (av::v::vs))` >>
  `!v. storage_trace_frame (kont v)` by
    simp[Abbr `kont`,evaluate_storage_trace_frame,storage_trace_frame_bind_all,
         storage_trace_frame_create_operands] >>
  `bind (bind (eval_expr cx e) (read_result cx)) kont p = (res,out)` by
    fs[Abbr `kont`,create_copy_source_cons] >>
  `(?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
   ?bs q G tn.
     bind (eval_expr cx e) (read_result cx) p = (INL (BytesV bs),q) /\
     kont (BytesV bs) q = (res,out) /\ valid_horizon cx st0 H q.storage_trace /\
     q.gas_obs = gas_explicit (ml ++ ma ++ rest) u.vs_gas_readings ++ tail /\
     expr_val_rel cx (BaseT (BytesT (Dynamic cap))) (BytesV bs) raw_op u /\
     eval_operand target_op u = SOME aw /\ (!x. target_op = Var x ==> not_fresh_at cu x) /\
     expr_sim_inv ce cx env q /\ local_ptrs_reserved ce cu /\
     (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at cu x) /\
     (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cu x) /\
     return_buf_frame d ce cu u /\ alloca_history fnc u /\
     (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
     (!f i z. frag_reachable ctx fnc u f i z ==> dalloca_fmp_headroom i z) /\
     (!h. valid_horizon cx st0 h q.storage_trace ==>
       stmt_state_rel h ctx fnc ce cx q u /\ storage_well_formed_on cx q (FST h) /\
       ghost_inv_at (DF h) lo d ce cx q G tn u) /\ ~u.vs_halted` by suspend "unwrap" >>
  pop_assum strip_assume_tac >- (disj1_tac >> qexists_tac `err` >> simp[]) >>
  suspend "finish"
QED

Resume blueprint_agreed_raw_payload[unwrap]:
  Cases_on `exprs_can_mutate ce later`
  >- (`expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,([]:(num # num) option list),fnc,shfnc) ce cx (expr_type e) e p
         (st0,ca,cm,sca,scm,vv,s,Gi,ti) ==>
       gas_completed_operand (DF,lo,gas_explicit_sites ctx shctx,ctx,fnc,[])
         tops cx st0 ca cm (eval_expr cx e) (p,s,Gi,ti)
         (create_operand_vv_post (DF,lo,d,ctx,fnc) ce cx e (p,ca,cm,s,vv,Gi,ti))` by
        (strip_tac >> first_assum irule >> simp[]) >>
      drule_all (PURE_REWRITE_RULE [GSYM create_operand_vv_post_def,ETA_AX]
        blueprint_raw_copied_at_cut_from_replay) >> strip_tac
      >- (disj1_tac >> qexists_tac `err` >> simp[]) >>
      disj2_tac >> qexistsl [`bs`,`q`,`G`,`tn`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,fnc,shfnc) ce cx (expr_type e) e p
      (st0,ca,cu,sca,scu,raw_op,s,Gi,ti) ==>
   gas_completed_operand (DF,lo,gas_explicit_sites ctx shctx,ctx,fnc,PG)
      tops cx st0 ca cu (bind (eval_expr cx e) (read_result cx)) (p,s,Gi,ti)
      (expr_sim_full_post (DF,lo,d,ctx,fnc) ce cx e (p,ca,cu,s,raw_op,Gi,ti))` by
    (strip_tac >> first_assum irule >> simp[]) >>
  drule_all blueprint_raw_retained_at_cut_from_replay >> strip_tac
  >- (disj1_tac >> qexists_tac `err` >> simp[]) >>
  disj2_tac >> qexistsl [`bs`,`q`,`G'`,`tn'`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume blueprint_agreed_raw_payload[finish]:
  drule_all blueprint_raw_finish_at_cut >> strip_tac >>
  drule_all blueprint_raw_source_length_le_capacity >> strip_tac >>
  drule expr_body_pre_static_facts >> strip_tac >>
  `body_const_cells_agree [(NONE,tops)] cx env q` by
    (irule body_const_cells_agree_expr_read >> goal_assum (drule_at Any) >> simp[]) >>
  `!z. (!x w. not_fresh_at cprep x /\ lookup_var x t = SOME w ==> lookup_var x z = SOME w) /\
    z.vs_labels = t.vs_labels ==>
    eval_operand len z = SOME (n2w (LENGTH bs)) /\
    w2n (n2w (LENGTH bs) : bytes32) < 2 ** 64` by
    (gen_tac >> strip_tac >> drule_all blueprint_raw_replayed_length_at_add >> simp[]) >>
  disj2_tac >> qexistsl [`bs`,`q`,`G`,`tn`] >>
  fs[Abbr `kont`] >> conj_tac >>
  qx_gen_tac `z` >> strip_tac >>
  first_assum (qspec_then `z` mp_tac) >> simp[]
QED

Finalise blueprint_agreed_raw_payload
